module E04_Elaborate

/// P03, module 04: surface AST to core term.
///
/// SUMMARY
///   Three jobs, and each is a place the surface language deliberately differs
///   from the core:
///
///   1. **Stack order reverses.** A surface signature reads bottom-to-top with
///      the top on the RIGHT (Forth convention, D05 §2); a core index list has
///      the top at the HEAD. `elab_sig` is the single place that flips, and it
///      is the bug the abandoned draft made — see D-05.
///   2. **Names resolve.** Surface strings become `word_id`s.
///   3. **Locals disappear.** `$x` compiles to `SPick`/`SRoll`; the core never
///      learns that locals existed (D05 §3.4).
///
/// LOCALS, CONCRETELY
///   The elaborator tracks a compile-time `shape` — one slot per stack
///   position, head = top, each optionally named. Reading `$x` means finding
///   its slot and emitting deep access past everything above it.
///
///   The pick-vs-roll choice comes from an occurrence count taken up front
///   (`E02.count_var`), which is what lets this work without a liveness
///   analysis:
///
///     * read **once**  -> `SRoll` (a move; consumes the slot, nothing to
///       clean up afterwards)
///     * read **twice or more** -> `SPick` each time (a copy, so the type must
///       be `Copy`), and the slot is dropped at end of body
///     * read **never** -> the slot is dropped at end of body
///
///   Dropping requires `Drop`, so a linear local that is never read is a type
///   error rather than a silent leak — which is the whole point of D-08.

open FStar.List.Tot
open M01_Kinds
open M03_Signatures
open M04_Effects
open M05_Terms
open M06_Typing
open E02_Ast

(* ------------------------------------------------------------------------ *)
(* Name environment                                                         *)
(* ------------------------------------------------------------------------ *)

/// A resolvable word. The signature is carried here as well as in M06's
/// `wenv` because the elaborator needs it to keep its shape model accurate,
/// before any typechecking happens.
type nentry = {
  n_name : string;
  n_id   : word_id;
  n_sig  : srow;
}

type nenv = list nentry

let rec lookup_name (e:nenv) (x:string) : Tot (option nentry) (decreases e) =
  match e with
  | []     -> None
  | n :: r -> if n.n_name = x then Some n else lookup_name r x

(* ------------------------------------------------------------------------ *)
(* Types                                                                    *)
(* ------------------------------------------------------------------------ *)

let prim_of_name (s:string) : Tot (option prim) =
  if s = "i8" then Some PI8 else if s = "i16" then Some PI16
  else if s = "i32" then Some PI32 else if s = "i64" then Some PI64
  else if s = "u8" then Some PU8 else if s = "u16" then Some PU16
  else if s = "u32" then Some PU32 else if s = "u64" then Some PU64
  else if s = "f32" then Some PF32 else if s = "f64" then Some PF64
  else if s = "bool" then Some PBool else if s = "unit" then Some PUnit
  else None

let rec elab_ty (t:sty) : Tot (either string dtype) (decreases (sty_size t)) =
  match t with
  | StyName n -> (match prim_of_name n with
                  | Some p -> Inr (TPrim p)
                  | None   -> Inl ("unknown type: " ^ n))
  | StyBox u  -> (match elab_ty u with Inl e -> Inl e | Inr d -> Inr (TBox d))
  | StyRc u   -> (match elab_ty u with Inl e -> Inl e | Inr d -> Inr (TRc d))
  | StyVar n  -> Inl ("generic type #" ^ n ^ " is not supported yet")

let rec elab_tys (ts:list sty) : Tot (either string (list dtype)) (decreases ts) =
  match ts with
  | []     -> Inr []
  | t :: r -> (match elab_ty t with
               | Inl e -> Inl e
               | Inr d -> (match elab_tys r with
                           | Inl e  -> Inl e
                           | Inr ds -> Inr (d :: ds)))

let rec param_tys (ps:list sparam) : Tot (list sty) (decreases ps) =
  match ps with
  | []     -> []
  | p :: r -> p.sp_ty :: param_tys r

(* ------------------------------------------------------------------------ *)
(* Signatures                                                               *)
(* ------------------------------------------------------------------------ *)

/// D-12: named parameters must occupy the topmost contiguous run — a SUFFIX in
/// surface order, since the top of the stack is on the right. Binding pops from
/// the top, so a suffix elaborates to a straight run of accesses; a named
/// parameter buried under unnamed ones would need shuffling out and back.
let rec named_suffix_ok (seen_named:bool) (ps:list sparam)
  : Tot bool (decreases ps) =
  match ps with
  | []     -> true
  | p :: r -> (match p.sp_name with
               | None   -> if seen_named then false else named_suffix_ok false r
               | Some _ -> named_suffix_ok true r)

/// THE REVERSAL. Surface lists run bottom-to-top; core lists run top-first.
let elab_sig (s:ssig) : Tot (either string srow) =
  if not (named_suffix_ok false s.ss_in)
  then Inl "named parameters must be the topmost inputs; reorder the signature or name the ones beneath"
  else match elab_tys (param_tys s.ss_in) with
       | Inl e    -> Inl e
       | Inr ins  -> (match elab_tys s.ss_out with
                      | Inl e     -> Inl e
                      | Inr outs  -> Inr ({ pre = rev ins; post = rev outs }))

(* ------------------------------------------------------------------------ *)
(* Compile-time stack shape                                                 *)
(* ------------------------------------------------------------------------ *)

type slot = { sl_name : option string; sl_ty : dtype }

/// Head = top, matching the core.
type shape = list slot

let rec anon_slots (ds:list dtype) : Tot shape (decreases ds) =
  match ds with
  | []     -> []
  | d :: r -> { sl_name = None; sl_ty = d } :: anon_slots r

/// Entry shape for a body: the signature's inputs, already reversed by
/// `elab_sig`, re-paired with their surface names.
let rec entry_shape (ps:list sparam) (ds:list dtype) : Tot shape (decreases ps) =
  match ps, ds with
  | p :: pr, d :: dr -> { sl_name = p.sp_name; sl_ty = d } :: entry_shape pr dr
  | _, _             -> []

let rec drop_n (n:nat) (sh:shape) : Tot (option shape) (decreases n) =
  if n = 0 then Some sh
  else match sh with
       | []     -> None
       | _ :: r -> drop_n (n - 1) r

let rec remove_at (i:nat) (sh:shape) : Tot shape (decreases sh) =
  match sh with
  | []     -> []
  | s :: r -> if i = 0 then r else s :: remove_at (i - 1) r

/// Locate a named slot: its index, the types of everything above it (top-first,
/// which is the order `SPick`/`SRoll` expect), and its own type.
let rec find_named (x:string) (above:list dtype) (i:nat) (sh:shape)
  : Tot (option (nat & list dtype & dtype)) (decreases sh) =
  match sh with
  | []     -> None
  | s :: r ->
    (match s.sl_name with
     | Some y -> if y = x then Some (i, rev above, s.sl_ty)
                 else find_named x (s.sl_ty :: above) (i + 1) r
     | None   -> find_named x (s.sl_ty :: above) (i + 1) r)

let rec first_named (above:list dtype) (i:nat) (sh:shape)
  : Tot (option (nat & list dtype & dtype)) (decreases sh) =
  match sh with
  | []     -> None
  | s :: r ->
    (match s.sl_name with
     | Some _ -> Some (i, rev above, s.sl_ty)
     | None   -> first_named (s.sl_ty :: above) (i + 1) r)

(* ------------------------------------------------------------------------ *)
(* Occurrence counts                                                        *)
(* ------------------------------------------------------------------------ *)

type counts = list (string & nat)

let rec lookup_count (cs:counts) (x:string) : Tot nat (decreases cs) =
  match cs with
  | []            -> 0
  | (y, n) :: r   -> if y = x then n else lookup_count r x

let rec build_counts (ps:list sparam) (body:list sterm) : Tot counts (decreases ps) =
  match ps with
  | []     -> []
  | p :: r -> (match p.sp_name with
               | None   -> build_counts r body
               | Some x -> (x, count_var_list x body) :: build_counts r body)

(* ------------------------------------------------------------------------ *)
(* Term elaboration                                                         *)
(* ------------------------------------------------------------------------ *)

/// Emit the access for one read of `$x`, and update the shape.
let elab_var (cs:counts) (sh:shape) (x:string)
  : Tot (either string (shape & term)) =
  match find_named x [] 0 sh with
  | None -> Inl ("unbound local $" ^ x)
  | Some (i, above, d) ->
    if lookup_count cs x = 1
    then
      /// Sole read: move it. Nothing is left behind to clean up.
      Inr (({ sl_name = None; sl_ty = d } :: remove_at i sh),
           TStack (SRoll above d))
    else if copyable d
    then
      /// Repeated read: copy, and leave the slot for the end-of-body drop.
      Inr (({ sl_name = None; sl_ty = d } :: sh), TStack (SPick above d))
    else
      Inl ("$" ^ x ^ " has a non-copyable type and is read more than once; \
            a linear local must be read exactly once")

let elab_lit (n:int) : Tot (either string term) =
  if -(pow2 63) <= n && n < pow2 63
  then Inr (TLit (LPrim PI64 n))
  else Inl ("integer literal out of range for i64: " ^ string_of_int n)

/// Measures: every edge below decreases the size component strictly, including
/// the two that cross between a term list and a branch list, because
/// `E02.sterm_lists_size` charges one per branch. The ranks are therefore
/// documentation of the intended ordering rather than load-bearing — unlike
/// M01's and M05's, where an empty sub-list makes them necessary.
let rec elab_terms (env:nenv) (cs:counts) (sh:shape) (acc:list term)
                   (ts:list sterm)
  : Tot (either string (shape & list term))
        (decreases %[sterms_size ts; 0]) =
  match ts with
  | [] -> Inr (sh, rev acc)
  | t :: rest ->
    (match t with
     | StInt n ->
       (match elab_lit n with
        | Inl e   -> Inl e
        | Inr trm -> elab_terms env cs
                       ({ sl_name = None; sl_ty = TPrim PI64 } :: sh)
                       (trm :: acc) rest)

     | StVar x ->
       (match elab_var cs sh x with
        | Inl e            -> Inl e
        | Inr (sh', trm)   -> elab_terms env cs sh' (trm :: acc) rest)

     /// The stack shuffles are polymorphic in the surface language but
     /// monomorphic in the core (D02 §5), so the elaborator instantiates them
     /// from the compile-time shape. This is also where their capability
     /// requirements are first reported, with a message naming the word the
     /// user actually typed.
     | StWord "dup" ->
       (match sh with
        | [] -> Inl "dup: the stack is empty"
        | s :: _ ->
          if not (copyable s.sl_ty)
          then Inl "dup: this value's type is not Copy"
          else elab_terms env cs ({ sl_name = None; sl_ty = s.sl_ty } :: sh)
                 (TStack (SDup s.sl_ty) :: acc) rest)

     | StWord "pop" ->
       (match sh with
        | [] -> Inl "pop: the stack is empty"
        | s :: sr ->
          if not (droppable s.sl_ty)
          then Inl "pop: this value's type is not Drop; consume it explicitly"
          else elab_terms env cs sr (TStack (SPop s.sl_ty) :: acc) rest)

     | StWord "swap" ->
       (match sh with
        | a :: b :: sr ->
          elab_terms env cs (b :: a :: sr)
            (TStack (SSwap a.sl_ty b.sl_ty) :: acc) rest
        | _ -> Inl "swap: needs two values on the stack")

     | StWord w ->
       (match lookup_name env w with
        | None -> Inl ("unknown word: " ^ w)
        | Some n ->
          (match drop_n (length n.n_sig.pre) sh with
           | None ->
             Inl ("stack underflow calling " ^ w ^ ": it needs "
                  ^ string_of_int (length n.n_sig.pre) ^ " inputs")
           | Some sh' ->
             elab_terms env cs (anon_slots n.n_sig.post @ sh')
               (TWord n.n_id :: acc) rest))

     | StBlock _ ->
       Inl "a { } block is only meaningful as a definition body or a branch"

     /// Case analysis. The scrutinee is a `bool` and nothing else, because
     /// `bool` is currently the only sum-shaped thing the surface language can
     /// put on the stack — `TInj` has no surface form yet. Branches are in TAG
     /// order (D-33), so the FALSE branch comes first, and `TBoolSum` is
     /// emitted here rather than spelled by the user.
     ///
     /// When sum syntax lands this case grows a `TSum variants` arm; the shape
     /// of the code does not otherwise change.
     | StCase bs ->
       (match sh with
        | [] -> Inl "if: the stack is empty; the condition must leave a bool"
        | s :: sr ->
          if s.sl_ty <> TPrim PBool
          then Inl "if: the condition must leave a bool on top of the stack"
          else if length bs <> 2
          then Inl "if: a bool has exactly two branches"
          else (match elab_branches env cs sr None [] bs with
                | Inl e -> Inl e
                | Inr (sh', bts) ->
                  elab_terms env cs sh'
                    (TCase bool_variants bts :: TBoolSum :: acc) rest)))

/// Elaborate each branch against the SAME entry shape and require them to
/// agree on the exit shape.
///
/// Agreement is equality of the modelled shape, which is stricter-looking than
/// `M06.srow_join` but means the same thing here: the model is one concrete
/// stack, so a branch reaching further beneath it simply leaves a shorter
/// list, and two branches agree exactly when those lists coincide. M06 then
/// re-derives the same fact row-polymorphically and independently.
and elab_branches (env:nenv) (cs:counts) (sh0:shape)
                  (expect:option shape) (acc:list term) (bs:list (list sterm))
  : Tot (either string (shape & list term))
        (decreases %[sterm_lists_size bs; 1]) =
  match bs with
  | [] -> (match expect with
           | None    -> Inl "if: no branches"
           | Some sh -> Inr (sh, rev acc))
  | b :: r ->
    (match elab_terms env cs sh0 [] b with
     | Inl e -> Inl e
     | Inr (sh1, ts) ->
       let ok = (match expect with None -> true | Some ex -> ex = sh1) in
       if not ok
       then Inl "the branches of an if leave the stack in different states"
       else elab_branches env cs sh0 (Some sh1) (seq_of ts :: acc) r)

/// Roll each surviving named slot to the top and pop it. Runs once, after the
/// body, and is the counterpart to the pick-based read strategy above.
///
/// Fuel rather than a structural measure: `remove_at` provably shrinks the
/// shape only when the index is in range, and encoding that would mean a
/// dependent return type on `first_named`. Since every iteration removes one
/// named slot, `length sh` is an exact bound.
let rec drop_named (fuel:nat) (sh:shape) (acc:list term)
  : Tot (either string (shape & list term)) (decreases fuel) =
  if fuel = 0 then Inr (sh, rev acc)
  else match first_named [] 0 sh with
       | None -> Inr (sh, rev acc)
       | Some (i, above, d) ->
         if not (droppable d)
         then Inl "a local of non-droppable type is left unconsumed at end of body"
         else drop_named (fuel - 1) (remove_at i sh)
                (TStack (SPop d) :: TStack (SRoll above d) :: acc)

(* ------------------------------------------------------------------------ *)
(* Signature inference                                                      *)
(* ------------------------------------------------------------------------ *)

/// A `define` with no `( … )` has its signature inferred from its body.
///
/// WHY THIS IS EASY HERE
///   Concatenative composition *is* signature composition (M03), so inference
///   needs no constraint solver and no generalisation step. Walk the body once,
///   modelling the stack; whenever the model runs dry, invent a variable and
///   record that the word must have consumed one more input. The variables so
///   invented, in the order they were pulled, are exactly the inferred `pre`.
///
///   Every word's signature is ground, so the only constraint that ever arises
///   is `variable := concrete type`. No variable is ever equated with another
///   variable, so the substitution is a flat map — no union-find, no occurs
///   check, no unifier.
///
/// TWO PASSES, DELIBERATELY
///   This pass computes types only; it emits no terms. The concrete elaborator
///   above then runs again over the same body with the inferred inputs in hand.
///   The alternative — emitting terms containing unresolved variables and
///   substituting afterwards — would mean a second, near-duplicate term type.
///   Running the tested elaborator twice is cheaper in code and in risk, and a
///   definition body is small.
///
/// WHAT IT CANNOT DO
///   A body whose stack effect is genuinely polymorphic (`{ dup }`, `{ swap }`)
///   leaves a variable unconstrained. That is not a failure of the algorithm:
///   the core is monomorphic (D02 §5), so there is no signature to infer. The
///   error says to write one out.
///
///   Per D01, inference is also *not* intended for words declared inside an
///   effect — an interface's whole purpose is to fix signatures ahead of any
///   implementation, so there is nothing to infer from. Nothing enforces that
///   yet because effect syntax does not exist; it belongs with D03's pass.

/// A modelled slot type: known, or a variable standing for something the body
/// pulls from beneath its own inputs.
type mty =
  | MV : nat -> mty
  | MT : dtype -> mty

type mslot = { m_name : option string; m_ty : mty }

noeq type ist = {
  /// The modelled stack, top-first.
  i_above : list mslot;
  /// Variables pulled from beneath, in pull order — which is top-first, since
  /// the shallowest is pulled first. This becomes `pre`.
  i_below : list mty;
  i_sub   : list (nat & dtype);
  i_next  : nat;
}

let ist0 : ist = { i_above = []; i_below = []; i_sub = []; i_next = 0 }

/// Take the top slot, inventing an input if the model has run dry.
let ipop (st:ist) : Tot (mslot & ist) =
  match st.i_above with
  | s :: r -> (s, { st with i_above = r })
  | []     ->
    let v = st.i_next in
    ({ m_name = None; m_ty = MV v },
     { st with i_below = st.i_below @ [MV v]; i_next = v + 1 })

let ipush (m:mty) (st:ist) : Tot ist =
  { st with i_above = { m_name = None; m_ty = m } :: st.i_above }

let iunify (w:string) (st:ist) (m:mty) (d:dtype) : Tot (either string ist) =
  let clash = Inl (w ^ ": this input does not match what the body puts there") in
  match m with
  | MT d' -> if d' = d then Inr st else clash
  | MV v  -> (match assoc v st.i_sub with
              | Some d' -> if d' = d then Inr st else clash
              | None    -> Inr ({ st with i_sub = (v, d) :: st.i_sub }))

/// `pre` is top-first and `ipop` yields top-first, so this consumes in order.
let rec iapply_pre (w:string) (st:ist) (pre:list dtype)
  : Tot (either string ist) (decreases pre) =
  match pre with
  | []     -> Inr st
  | d :: r -> let (s, st1) = ipop st in
              (match iunify w st1 s.m_ty d with
               | Inl e   -> Inl e
               | Inr st2 -> iapply_pre w st2 r)

/// `post` is top-first, so its head must be pushed last.
let rec ipush_post (post:list dtype) (st:ist) : Tot ist (decreases post) =
  match post with
  | []     -> st
  | d :: r -> ipush (MT d) (ipush_post r st)

let rec ifind (x:string) (i:nat) (sh:list mslot)
  : Tot (option (nat & mty)) (decreases sh) =
  match sh with
  | []     -> None
  | s :: r -> (match s.m_name with
               | Some y -> if y = x then Some (i, s.m_ty) else ifind x (i + 1) r
               | None   -> ifind x (i + 1) r)

let rec iremove_at (i:nat) (sh:list mslot) : Tot (list mslot) (decreases sh) =
  match sh with
  | []     -> []
  | s :: r -> if i = 0 then r else s :: iremove_at (i - 1) r

(* --- branches ----------------------------------------------------------- *)

/// The slots for variables pulled from beneath since a mark, in pull order.
///
/// Each branch of a case must start from the same modelled stack, but a branch
/// that pulls from below extends `i_below` for good — the slot it pulled is a
/// real input of the whole definition, and a later branch reaching the same
/// depth must find the SAME variable there rather than invent a second one.
/// Restoring these on top of the entry shape is what arranges that.
let rec islots_from (n:nat) (below:list mty)
  : Tot (list mslot) (decreases below) =
  match below with
  | []     -> []
  | m :: r -> if n = 0
              then { m_name = None; m_ty = m } :: islots_from 0 r
              else islots_from (n - 1) r

/// Compare one modelled slot from two branches, recording `variable :=
/// concrete` when one side knows more than the other.
///
/// Two distinct variables never meet here: a variable in a given position came
/// from a pull at a given depth, and `islots_from` gives every branch the same
/// one. So this stays inside D-31 — the only constraint form is still
/// `variable := concrete type`, and there is no unifier.
let imatch1 (st:ist) (a:mty) (b:mty) : Tot (either string ist) =
  let clash = Inl "the branches of an if leave different types on the stack" in
  match a, b with
  | MT d1, MT d2 -> if d1 = d2 then Inr st else clash
  | MT d,  MV v  -> iunify "if" st (MV v) d
  | MV v,  MT d  -> iunify "if" st (MV v) d
  | MV v,  MV w  -> if v = w then Inr st else clash

let rec imatch (st:ist) (xs:list mslot) (ys:list mslot)
  : Tot (either string ist) (decreases xs) =
  match xs, ys with
  | [], []           -> Inr st
  | x :: xr, y :: yr ->
    (match imatch1 st x.m_ty y.m_ty with
     | Inl e   -> Inl e
     | Inr st' -> imatch st' xr yr)
  | _ -> Inl "the branches of an if leave different numbers of values on the stack"

/// Mirrors `elab_terms` slot-for-slot, minus term emission. Capability checks
/// are deliberately absent: this pass decides types, and pass 2 — which sees
/// concrete ones — is where `Copy`/`Drop` violations get reported.
let rec infer_terms (env:nenv) (cs:counts) (st:ist) (ts:list sterm)
  : Tot (either string ist) (decreases %[sterms_size ts; 0]) =
  match ts with
  | [] -> Inr st
  | t :: rest ->
    (match t with
     | StInt _ -> infer_terms env cs (ipush (MT (TPrim PI64)) st) rest

     | StVar x ->
       (match ifind x 0 st.i_above with
        | None -> Inl ("unbound local $" ^ x)
        | Some (i, m) ->
          let top = { m_name = None; m_ty = m } in
          let above' = if lookup_count cs x = 1
                       then top :: iremove_at i st.i_above
                       else top :: st.i_above in
          infer_terms env cs ({ st with i_above = above' }) rest)

     | StWord "dup" ->
       let (s, st1) = ipop st in
       infer_terms env cs
         ({ st1 with i_above = { m_name = None; m_ty = s.m_ty } :: s :: st1.i_above })
         rest

     | StWord "pop" ->
       let (_, st1) = ipop st in
       infer_terms env cs st1 rest

     | StWord "swap" ->
       let (a, st1) = ipop st in
       let (b, st2) = ipop st1 in
       infer_terms env cs ({ st2 with i_above = b :: a :: st2.i_above }) rest

     | StWord w ->
       (match lookup_name env w with
        | None -> Inl ("unknown word: " ^ w)
        | Some n ->
          (match iapply_pre w st n.n_sig.pre with
           | Inl e   -> Inl e
           | Inr st1 -> infer_terms env cs (ipush_post n.n_sig.post st1) rest))

     | StBlock _ ->
       Inl "a { } block is only meaningful as a definition body or a branch"

     /// Mirrors `elab_terms`' case exactly, minus term emission. The scrutinee
     /// may be a variable here, in which case running the case is what
     /// constrains it to `bool`.
     | StCase bs ->
       let (s, st1) = ipop st in
       (match iunify "if" st1 s.m_ty (TPrim PBool) with
        | Inl _   ->
          Inl "if: the condition must leave a bool on top of the stack"
        | Inr st2 ->
          if length bs <> 2
          then Inl "if: a bool has exactly two branches"
          else (match infer_branches_i env cs st2.i_above (length st2.i_below)
                        st2 None bs with
                | Inl e   -> Inl e
                | Inr st3 -> infer_terms env cs st3 rest)))

/// Run each branch from the same entry stack, threading the accumulated
/// substitution and pulled inputs forward, and require the branches to agree.
///
/// `above0` is the modelled stack at the point of the case and `mark` is how
/// much had been pulled from beneath before it; together they let a later
/// branch see the same variables an earlier one invented (`islots_from`).
and infer_branches_i (env:nenv) (cs:counts) (above0:list mslot) (mark:nat)
                     (st:ist) (expect:option (list mslot))
                     (bs:list (list sterm))
  : Tot (either string ist) (decreases %[sterm_lists_size bs; 1]) =
  match bs with
  | [] -> (match expect with
           | None    -> Inl "if: no branches"
           | Some ex -> Inr ({ st with i_above = ex }))
  | b :: r ->
    let entry = { st with i_above = above0 @ islots_from mark st.i_below } in
    (match infer_terms env cs entry b with
     | Inl e    -> Inl e
     | Inr st'  ->
       (match expect with
        | None    ->
          infer_branches_i env cs above0 mark st' (Some st'.i_above) r
        | Some ex ->
          (match imatch st' ex st'.i_above with
           | Inl e    -> Inl e
           | Inr st'' ->
             infer_branches_i env cs above0 mark st'' (Some ex) r)))

let rec iresolve (su:list (nat & dtype)) (ms:list mty)
  : Tot (either string (list dtype)) (decreases ms) =
  match ms with
  | []     -> Inr []
  | m :: r ->
    let d0 = (match m with MT d -> Some d | MV v -> assoc v su) in
    (match d0 with
     | None   -> Inl "cannot infer this signature: a stack slot is never \
                      constrained to a concrete type, so the body is \
                      polymorphic and the core is not; write the signature out"
     | Some d -> (match iresolve su r with
                  | Inl e  -> Inl e
                  | Inr ds -> Inr (d :: ds)))

/// Named slots surviving the body are popped by `drop_named`, so they are not
/// outputs.
let rec ianon (sh:list mslot) : Tot (list mty) (decreases sh) =
  match sh with
  | []     -> []
  | s :: r -> (match s.m_name with
               | Some _ -> ianon r
               | None   -> s.m_ty :: ianon r)

let infer_sig (env:nenv) (body:list sterm) : Tot (either string srow) =
  match infer_terms env [] ist0 body with
  | Inl e -> Inl e
  | Inr st ->
    (match iresolve st.i_sub st.i_below with
     | Inl e   -> Inl e
     | Inr pre ->
       (match iresolve st.i_sub (ianon st.i_above) with
        | Inl e    -> Inl e
        | Inr post -> Inr ({ pre = pre; post = post })))

(* ------------------------------------------------------------------------ *)
(* Declarations                                                             *)
(* ------------------------------------------------------------------------ *)

/// Elaborate a definition body against its declared signature.
let elab_define (env:nenv) (sg:ssig) (body:list sterm)
  : Tot (either string (srow & term)) =
  match elab_sig sg with
  | Inl e -> Inl e
  | Inr row ->
    let sh0 = entry_shape (rev sg.ss_in) row.pre in
    let cs  = build_counts sg.ss_in body in
    (match elab_terms env cs sh0 [] body with
     | Inl e -> Inl e
     | Inr (sh1, ts1) ->
       (match drop_named (length sh1) sh1 [] with
        | Inl e -> Inl e
        | Inr (_, ts2) -> Inr (row, seq_of (ts1 @ ts2))))

/// Elaborate a definition with no written signature: infer one, then elaborate
/// the body against it with the ordinary concrete pass. There are no named
/// parameters in this form — naming happens in a signature — so the entry shape
/// is anonymous and no end-of-body drop is needed.
let elab_define_infer (env:nenv) (body:list sterm)
  : Tot (either string (srow & term)) =
  match infer_sig env body with
  | Inl e -> Inl e
  | Inr row ->
    (match elab_terms env [] (anon_slots row.pre) [] body with
     | Inl e       -> Inl e
     | Inr (_, ts) -> Inr (row, seq_of ts))

/// Elaborate a bare expression against a known incoming stack shape.
let elab_expr (env:nenv) (incoming:list dtype) (body:list sterm)
  : Tot (either string term) =
  match elab_terms env [] (anon_slots incoming) [] body with
  | Inl e          -> Inl e
  | Inr (_, ts)    -> Inr (seq_of ts)
