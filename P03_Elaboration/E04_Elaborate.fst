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

let rec elab_terms (env:nenv) (cs:counts) (sh:shape) (acc:list term)
                   (ts:list sterm)
  : Tot (either string (shape & list term)) (decreases ts) =
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
       Inl "a { } block is only meaningful as a definition body in this pass")

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

/// Elaborate a bare expression against a known incoming stack shape.
let elab_expr (env:nenv) (incoming:list dtype) (body:list sterm)
  : Tot (either string term) =
  match elab_terms env [] (anon_slots incoming) [] body with
  | Inl e          -> Inl e
  | Inr (_, ts)    -> Inr (seq_of ts)
