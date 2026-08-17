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
/// For `eff_case`, the effect a `case` dispatches through (D-68). P03 already
/// depends on P02 -- `E05` opens `R01_Runtime` -- so this adds no new edge.
open R03_Prelude
open E02_Ast

(* ------------------------------------------------------------------------ *)
(* Name environment                                                         *)
(* ------------------------------------------------------------------------ *)

/// A resolvable word. The signature is carried here as well as in M06's
/// `wenv` because the elaborator needs it to keep its shape model accurate,
/// before any typechecking happens.
///
/// `n_op` is `Some e` when the word is an OPERATION of effect `e`. Nothing
/// else distinguishes the two: an operation is called as `TWord` and typed by
/// the same rule, which is D03's unification showing up as the absence of a
/// second case rather than as a feature. The field exists only so that
/// `handle` can check an implementation is implementing something.
type nentry = {
  n_name : string;
  n_id   : word_id;
  n_sig  : srow;
  n_op   : option eff_id;
}

/// A generic definition, stored as a TEMPLATE (D-79). Nothing is elaborated
/// when it is declared: rigid type variables are not `M01.dtype`s, so there is
/// no monomorphic body to check until a call site supplies the types. The body
/// is therefore checked at INSTANTIATION, C++ and not ML, and the trade is what
/// keeps the core free of a variable case.
type gentry = {
  g_name   : string;
  g_params : list string;
  g_sig    : ssig;
  g_body   : list sterm;
}

let rec lookup_gen_in (gs:list gentry) (x:string)
  : Tot (option gentry) (decreases gs) =
  match gs with
  | []     -> None
  | g :: r -> if g.g_name = x then Some g else lookup_gen_in r x

/// What `E04` hands back for `E06` to install. `case` operations travelled this
/// channel already (D-68); widening its element to a variant is what lets a
/// generic instantiation use the same route without threading a second
/// accumulator through `elab_terms`, `elab_branches`, `elab_impls` and
/// `elab_handle_parts`.
noeq type gdecl =
  /// An operation a `case` site dispatches through.
  | GOp   : op_id -> op_decl -> gdecl
  /// Instantiate generic `name` at `sub`. `id` is the SPLICE KEY the call site
  /// emitted as `TWord id`, taken from its own one-id budget; `E06` builds the
  /// instance and substitutes its body for that call (D-83). No word with this
  /// id is ever installed, which is why one id suffices however large the
  /// generic is.
  | GInst : word_id -> string -> tsub -> gdecl

/// Declared types, by name (D-89).
///
/// THE VALUE IS THE `dtype` ITSELF, not a declaration to be resolved. That is
/// enough only for NON-RECURSIVE types: a recursive one needs `M01.TName`
/// pointing at a `nom_id`, which needs `wenv` to carry a table from `nom_id` to
/// representation — the very thing N02 Q-13 says is required and calls a design
/// call. So `data` refuses a self-reference, with a message rather than a loop.
///
/// It is passed to `elab_ty` and friends as a bare table rather than as the
/// whole `nenv`, because type elaboration needs nothing else — not words, not
/// effects, not generics — and keeping the dependency at its real size is what
/// lets `elab_ty` stay callable from `explicit_sub`, which has no environment.
type tenv = list (string & dtype)

let rec lookup_ty_in (ts:tenv) (x:string) : Tot (option dtype) (decreases ts) =
  match ts with
  | []          -> None
  | (n, d) :: r -> if n = x then Some d else lookup_ty_in r x

/// Names live in four namespaces because none of them can be called the way a
/// word can — `handle E` names an effect, `f[…]` names a template, and a type
/// appears only in a signature.
type nenv = {
  ne_words : list nentry;
  ne_effs  : list (string & eff_id);
  /// Generic templates (D-79). A third namespace, because a generic has no
  /// `word_id` and cannot be called until it is instantiated.
  ne_gens  : list gentry;
  /// Declared types (D-89).
  ne_types : tenv;
}

let rec lookup_word_in (ws:list nentry) (x:string)
  : Tot (option nentry) (decreases ws) =
  match ws with
  | []     -> None
  | n :: r -> if n.n_name = x then Some n else lookup_word_in r x

let lookup_name (e:nenv) (x:string) : Tot (option nentry) =
  lookup_word_in e.ne_words x

let rec lookup_eff_in (es:list (string & eff_id)) (x:string)
  : Tot (option eff_id) (decreases es) =
  match es with
  | []            -> None
  | (n, i) :: r   -> if n = x then Some i else lookup_eff_in r x

let lookup_eff (e:nenv) (x:string) : Tot (option eff_id) =
  lookup_eff_in e.ne_effs x

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
  else if s = "str" then Some PStr
  else None

let rec elab_ty (te:tenv) (t:sty) : Tot (either string dtype) (decreases (sty_size t)) =
  match t with
  /// A primitive first, so no `data` declaration can shadow `i64`. Names in
  /// this table are the language's own and are not the program's to rebind —
  /// unlike words, which shadow freely (D-32).
  | StyName n -> (match prim_of_name n with
                  | Some p -> Inr (TPrim p)
                  | None   -> (match lookup_ty_in te n with
                               | Some d -> Inr d
                               | None   -> Inl ("unknown type: " ^ n)))
  | StyBox u  -> (match elab_ty te u with Inl e -> Inl e | Inr d -> Inr (TBox d))
  | StyRc u   -> (match elab_ty te u with Inl e -> Inl e | Inr d -> Inr (TRc d))
  /// A variable that survived to here was never bound by an instantiation
  /// (D-79). Inside a generic's stored body that is impossible — `E06` rewrites
  /// every parameter before elaborating — so this reports the one case that can
  /// reach it: a `#T` written in a signature that declares no such parameter.
  | StyVar n  -> Inl ("#" ^ n ^ " is not a type parameter of this definition")
  /// Already elaborated: the type an instantiation substituted in.
  | StyFixed d -> Inr d

let rec elab_tys (te:tenv) (ts:list sty)
  : Tot (either string (list dtype)) (decreases ts) =
  match ts with
  | []     -> Inr []
  | t :: r -> (match elab_ty te t with
               | Inl e -> Inl e
               | Inr d -> (match elab_tys te r with
                           | Inl e  -> Inl e
                           | Inr ds -> Inr (d :: ds)))

let rec param_tys (ps:list sparam) : Tot (list sty) (decreases ps) =
  match ps with
  | []     -> []
  | p :: r -> p.sp_ty :: param_tys r

(* ------------------------------------------------------------------------ *)
(* Matching a generic's declared types against a call site                  *)
(* ------------------------------------------------------------------------ *)

/// Bind a generic's type parameters by matching its declared inputs against
/// what is actually on the modelled stack (D-77, D-79).
///
/// MATCHING, NOT UNIFICATION, and the asymmetry is the whole reason the
/// language needs no unifier. The pattern is a surface `sty` and may contain
/// variables; the target is a `M01.dtype` from the stack model and never can.
/// So every constraint is `flexible := rigid`: a flat map, no occurs check
/// (the target holds no variables to occur in), no union-find (there are no
/// flexible-flexible constraints), no constraint graph.
///
/// A variable already bound must match what it was bound to, which is what
/// makes `( #T #T -- #T )` mean both inputs have the same type.
let rec match_ty (te:tenv) (su:tsub) (pat:sty) (d:dtype)
  : Tot (option tsub) (decreases (sty_size pat)) =
  match pat with
  | StyVar n   -> (match assoc n su with
                   | Some (StyFixed d') -> if d' = d then Some su else None
                   | Some _             -> None
                   | None               -> Some ((n, StyFixed d) :: su))
  | StyFixed d' -> if d' = d then Some su else None
  /// A declared type matches by the representation it names, which is right
  /// while a type name is a pure abbreviation. It stops being right the moment
  /// two `data` declarations can have the same representation and still be
  /// different types — see the note on nominality at `elab_data` (D-89).
  | StyName n  -> (match prim_of_name n, d with
                   | Some p, TPrim q -> if p = q then Some su else None
                   | Some _, _       -> None
                   | None, _         -> (match lookup_ty_in te n with
                                         | Some d' -> if d' = d then Some su else None
                                         | None    -> None))
  | StyBox u   -> (match d with
                   | TBox d' -> match_ty te su u d'
                   | _       -> None)
  | StyRc u    -> (match d with
                   | TRc d'  -> match_ty te su u d'
                   | _       -> None)

/// Left to right over the declared inputs, TOP FIRST — the caller reverses the
/// surface list, since the stack model runs top-first and a signature does not.
let rec match_tys (te:tenv) (su:tsub) (pats:list sty) (ds:list dtype)
  : Tot (option tsub) (decreases pats) =
  match pats, ds with
  | [], _            -> Some su
  | p :: pr, d :: dr -> (match match_ty te su p d with
                         | None     -> None
                         | Some su' -> match_tys te su' pr dr)
  | _, []            -> None

/// Every parameter must be determined by the inputs. One that is not appears
/// only in the outputs, which the call site cannot see — `( -- #T )` is a
/// request to invent a type, and refusing it is what keeps instantiation a
/// matching problem rather than an inference problem.
let rec all_bound (su:tsub) (ps:list string) : Tot (option string) (decreases ps) =
  match ps with
  | []     -> None
  | p :: r -> if None? (assoc p su) then Some p else all_bound su r

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
let elab_sig (te:tenv) (s:ssig) : Tot (either string srow) =
  if not (named_suffix_ok false s.ss_in)
  then Inl "named parameters must be the topmost inputs; reorder the signature or name the ones beneath"
  else match elab_tys te (param_tys s.ss_in) with
       | Inl e    -> Inl e
       | Inr ins  -> (match elab_tys te s.ss_out with
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

/// The inverse: a modelled shape as a plain segment. Needed since D-68, because
/// a `case` now declares operations at the shape either side of it.
let rec slot_tys (sh:shape) : Tot (list dtype) (decreases sh) =
  match sh with
  | []     -> []
  | s :: r -> s.sl_ty :: slot_tys r

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
           TPrimOp (PStack (SRoll above d)))
    else if copyable d
    then
      /// Repeated read: copy, and leave the slot for the end-of-body drop.
      Inr (({ sl_name = None; sl_ty = d } :: sh), TPrimOp (PStack (SPick above d)))
    else
      Inl ("$" ^ x ^ " has a non-copyable type and is read more than once; \
            a linear local must be read exactly once")

/// Resolve a `with`'s rebindings to word ids, requiring EQUAL SIGNATURES.
///
/// Effects may differ freely — a replacement performing effects the original
/// did not is the main reason to rebind at all, and `M06.infer` recomputes the
/// row from the substituted term. What may not differ is the stack effect,
/// because the body is elaborated against the ORIGINAL one.
///
/// This check is the hypothesis of M11's obligation E7, enforced here because
/// E7 is stated and not yet proved. It becomes redundant, not wrong, when it is.
let rec resolve_rebinds (env:nenv) (su:list (string & string))
  : Tot (either string (list (word_id & word_id))) (decreases su) =
  match su with
  | [] -> Inr []
  | (a, b) :: r ->
    (match lookup_name env a, lookup_name env b with
     | None, _ -> Inl ("with: unknown word: " ^ a)
     | _, None -> Inl ("with: unknown word: " ^ b)
     | Some na, Some nb ->
       /// CHECKED HERE FOR THE MESSAGE, decided by `M06.infer_impls` (D-76).
       /// A `with` is a Dictionary handler, so the replacement is an
       /// implementation and M06 already types it at the operation's declared
       /// signature — this test is redundant for soundness and kept because
       /// "their signatures differ" locates the mistake, where the typing
       /// failure surfaces as "this definition does not typecheck".
       ///
       /// It is deliberately the same test M06 makes rather than the stricter
       /// equality it used to be: `impl_frame` accepts a replacement that
       /// reaches less deep than the operation declares (D-68), and rejecting
       /// one here would refuse a program the core accepts.
       if None? (impl_frame nb.n_sig []
                   ({ op_pre = na.n_sig.pre; op_post = na.n_sig.post }))
       then Inl ("with: " ^ b ^ " cannot replace " ^ a
                 ^ "; their signatures differ")
       else (match resolve_rebinds env r with
             | Inl e   -> Inl e
             | Inr ids -> Inr ((na.n_id, nb.n_id) :: ids)))

/// The rebindings as handler implementations: replacing `a` by `b` is
/// implementing the Dictionary operation `a` as a call to `b`.
let rec rebind_impls (ids:list (word_id & word_id))
  : Tot (list (op_id & term)) (decreases ids) =
  match ids with
  | []            -> []
  | (a, b) :: r   -> (a, TWord b) :: rebind_impls r

(* ------------------------------------------------------------------------ *)
(* Generic call sites                                                       *)
(* ------------------------------------------------------------------------ *)

/// The substitution an explicit instantiation writes out (D-82).
///
/// The types are elaborated HERE, to `StyFixed`, which is why the explicit and
/// implicit paths can then share everything: `match_ty` treats a parameter
/// already bound to a `StyFixed` as a constraint to check rather than a binding
/// to make, so passing this as `match_tys`' starting substitution turns the
/// written types into an assertion about the stack for free.
let rec explicit_sub (te:tenv) (ps:list string) (tys:list sty)
  : Tot (either string tsub) (decreases ps) =
  match ps, tys with
  | [], []           -> Inr []
  | p :: pr, t :: tr ->
    (match elab_ty te t with
     | Inl e -> Inl e
     | Inr d -> (match explicit_sub te pr tr with
                 | Inl e  -> Inl e
                 | Inr su -> Inr ((p, StyFixed d) :: su)))
  | _, _             -> Inl "arity"

/// Resolve one generic call site to a substitution and an instantiated
/// signature. `su0` is `[]` for `f` and pre-filled for `f[…]`, and that is the
/// ONLY difference between the two forms — everything after it is shared, so an
/// explicit instantiation is checked against the stack exactly as an implicit
/// one is rather than believed.
let gen_call (te:tenv) (w:string) (g:gentry) (su0:tsub) (sh:shape)
  : Tot (either string (tsub & srow)) =
  let pats = rev (param_tys g.g_sig.ss_in) in
  if length pats > length sh
  then Inl ("stack underflow calling " ^ w ^ ": it needs "
            ^ string_of_int (length pats) ^ " inputs")
  else
    (match match_tys te su0 pats (slot_tys sh) with
     | None -> Inl (w ^ ": the stack does not match its declared inputs")
     | Some su ->
       (match all_bound su g.g_params with
        | Some p ->
          Inl (w ^ ": #" ^ p ^ " is not determined by the inputs; write the \
                types at the call site, as in " ^ w ^ "[i64]")
        | None ->
          (match elab_sig te (subst_ssig su g.g_sig) with
           | Inl e   -> Inl (w ^ ": " ^ e)
           | Inr row -> Inr (su, row))))

let elab_lit (n:int) : Tot (either string term) =
  if -(pow2 63) <= n && n < pow2 63
  then Inr (TPrimOp (PLit (LPrim PI64 n)))
  else Inl ("integer literal out of range for i64: " ^ string_of_int n)

/// Roll each surviving named slot to the top and pop it. Runs after a body and
/// after a `try` block, and is the counterpart to the pick-based read strategy
/// above: a repeated read leaves its slot behind, and this is what clears it.
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
                (TPrimOp (PStack (SPop d)) :: TPrimOp (PStack (SRoll above d)) :: acc)

/// The named locals of `sh`, topmost first and without repeats, keeping only
/// those `blk` actually reads. Used to decide what a `try` block closes over
/// (D-87); a name that appears twice in the shape is a shadowed local, and the
/// topmost is the one in scope, so the first occurrence is the right one.
let rec mentioned_locals (sh:shape) (seen:list string) (blk:list sterm)
  : Tot (list string) (decreases sh) =
  match sh with
  | []     -> []
  | s :: r ->
    (match s.sl_name with
     | Some x ->
       if mem x seen || count_var_list x blk = 0
       then mentioned_locals r seen blk
       else x :: mentioned_locals r (x :: seen) blk
     | None   -> mentioned_locals r seen blk)

/// Copy each of `xs` to the top of the stack, and report the shape the copies
/// form (topmost first, still named) alongside the terms that build it.
///
/// ALWAYS A COPY, NEVER A MOVE, which is the same choice D-41 made for branch
/// reads and for the same kind of reason. A `try` block may abort, and an abort
/// cuts the stack back past whatever the block was given — so a moved local
/// would be destroyed on a path the reader did not write. Copying costs the
/// requirement that the type be `Copy`, and that requirement is honest.
///
/// `sh` grows as we go so that each `find_named` measures against the stack as
/// it will actually be; the enclosing shape underneath is untouched, because
/// every emitted term is a `pick`.
let rec copy_locals (sh:shape) (blk:shape) (acc:list term) (xs:list string)
  : Tot (either string (shape & list term)) (decreases xs) =
  match xs with
  | []     -> Inr (blk, acc)
  | x :: r ->
    (match find_named x [] 0 sh with
     | None -> Inl ("unbound local $" ^ x)
     | Some (i, above, d) ->
       if not (copyable d)
       then Inl ("$" ^ x ^ " has a non-copyable type and cannot be read inside a \
                  try block; the block runs on its own stack, so its locals are \
                  copied into it")
       else
         let s = { sl_name = Some x; sl_ty = d } in
         copy_locals (s :: sh) (s :: blk)
           (TPrimOp (PStack (SPick above d)) :: acc) r)

/// Measures: every edge below decreases the size component strictly, including
/// the two that cross between a term list and a branch list, because
/// `E02.sterm_lists_size` charges one per branch. The ranks are therefore
/// documentation of the intended ordering rather than load-bearing — unlike
/// M01's and M05's, where an empty sub-list makes them necessary.
let rec elab_terms (env:nenv) (cs:counts) (base:nat) (sh:shape) (acc:list term)
                   (dacc:list gdecl) (ts:list sterm)
  : Tot (either string (shape & list term & list gdecl))
        (decreases %[sterms_size ts; 0]) =
  match ts with
  | [] -> Inr (sh, rev acc, dacc)
  | t :: rest ->
    (match t with
     | StInt n ->
       (match elab_lit n with
        | Inl e   -> Inl e
        | Inr trm -> elab_terms env cs (base + sterm_size t)
                       ({ sl_name = None; sl_ty = TPrim PI64 } :: sh)
                       (trm :: acc) dacc rest)

     /// No range check and no failure case, unlike `StInt`: `E01` has already
     /// decoded the escapes, so every `StStr` is a valid `str` (D-65).
     | StStr s ->
       elab_terms env cs (base + sterm_size t)
         ({ sl_name = None; sl_ty = TPrim PStr } :: sh)
         (TPrimOp (PLit (LPrim PStr s)) :: acc) dacc rest

     | StVar x ->
       (match elab_var cs sh x with
        | Inl e            -> Inl e
        | Inr (sh2, trm)   -> elab_terms env cs (base + sterm_size t) sh2 (trm :: acc) dacc rest)

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
          else elab_terms env cs (base + sterm_size t)
                 ({ sl_name = None; sl_ty = s.sl_ty } :: sh)
                 (TPrimOp (PStack (SDup s.sl_ty)) :: acc) dacc rest)

     | StWord "pop" ->
       (match sh with
        | [] -> Inl "pop: the stack is empty"
        | s :: sr ->
          if not (droppable s.sl_ty)
          then Inl "pop: this value's type is not Drop; consume it explicitly"
          else elab_terms env cs (base + sterm_size t) sr
                 (TPrimOp (PStack (SPop s.sl_ty)) :: acc) dacc rest)

     | StWord "swap" ->
       (match sh with
        | a :: b :: sr ->
          elab_terms env cs (base + sterm_size t) (b :: a :: sr)
            (TPrimOp (PStack (SSwap a.sl_ty b.sl_ty)) :: acc) dacc rest
        | _ -> Inl "swap: needs two values on the stack")

     /// A GENERIC CALL SITE EMITS A PLACEHOLDER AND A REQUEST (D-79, D-83).
     ///
     /// `TWord base` is not a call to a word: no such word is ever installed.
     /// It is a SPLICE KEY, and `E06` replaces it with `TSpecialize body` once
     /// it has elaborated the instance — which is why the call site needs only
     /// its own one-id budget however large the generic is, and why an instance
     /// gets no dictionary entry. "Generics erase at elaboration" is that
     /// substitution, and the `TSpecialize` it leaves is the term that says so.
     | StWordAt w tys ->
       (match lookup_gen_in env.ne_gens w with
        | None -> Inl (w ^ " is not generic, so it takes no type arguments")
        | Some g ->
          if length g.g_params <> length tys
          then Inl (w ^ " has " ^ string_of_int (length g.g_params)
                    ^ " type parameters but was given "
                    ^ string_of_int (length tys))
          else
            (match explicit_sub env.ne_types g.g_params tys with
             | Inl e   -> Inl (w ^ ": " ^ e)
             | Inr su0 ->
               (match gen_call env.ne_types w g su0 sh with
                | Inl e -> Inl e
                | Inr (su, row) ->
                  (match drop_n (length row.pre) sh with
                   | None -> Inl ("stack underflow calling " ^ w)
                   | Some sh' ->
                     elab_terms env cs (base + sterm_size t)
                       (anon_slots row.post @ sh')
                       (TWord base :: acc) (GInst base w su :: dacc) rest))))

     | StWord w ->
       (match lookup_gen_in env.ne_gens w with
        /// The implicit form. Identical to `StWordAt` from `gen_call` onward;
        /// the types are recovered from the modelled stack instead of written.
        | Some g ->
          (match gen_call env.ne_types w g [] sh with
           | Inl e -> Inl e
           | Inr (su, row) ->
             (match drop_n (length row.pre) sh with
              | None -> Inl ("stack underflow calling " ^ w)
              | Some sh' ->
                elab_terms env cs (base + sterm_size t)
                  (anon_slots row.post @ sh')
                  (TWord base :: acc) (GInst base w su :: dacc) rest))

        | None ->
          (match lookup_name env w with
           | None -> Inl ("unknown word: " ^ w)
           | Some n ->
             (match drop_n (length n.n_sig.pre) sh with
              | None ->
                Inl ("stack underflow calling " ^ w ^ ": it needs "
                     ^ string_of_int (length n.n_sig.pre) ^ " inputs")
              | Some sh' ->
                elab_terms env cs (base + sterm_size t)
                  (anon_slots n.n_sig.post @ sh')
                  (TWord n.n_id :: acc) dacc rest)))

     | StBlock _ ->
       Inl "a { } block is only meaningful as a definition body or a branch"

     /// Case analysis. The scrutinee is a `bool` and nothing else, because
     /// `bool` is currently the only sum-shaped thing the surface language can
     /// put on the stack — `PInj` has no surface form yet. Branches are in TAG
     /// order (D-33), so the FALSE branch comes first, and `TPrimOp PBoolSum` is
     /// emitted here rather than spelled by the user.
     ///
     /// When sum syntax lands this case grows a `TSum variants` arm; the shape
     /// of the code does not otherwise change.
     /// A CASE IS A HANDLER (D-68). The branches become the implementations of
     /// two freshly declared operations, and what runs in the handler's body is
     /// a single `TDispatch` that performs whichever one the tag selects.
     ///
     /// IDS COME FROM A POSITIONAL BUDGET, not from a threaded counter. Each
     /// term gets `base` and passes `base + sterm_size t` to its successor, so
     /// distinct sites get distinct ranges without the elaborator carrying
     /// mutable state — and `sterm_size (StCase bs)` is `1 + length bs + …`,
     /// which is exactly the `1 + n` ids a case needs for itself. The effect id
     /// is shared by every case site (`eff_case`) and does not need to be
     /// fresh: an inner handler that does not implement an outer case's
     /// operation forwards it outward, which is `M04.fwd_impl` and
     /// `R02.find_handler` doing what they already do.
     ///
     /// The declarations are at the FULL modelled shape either side, which is
     /// deeper than necessary — the tightest declaration would strip the common
     /// suffix `sr` and `sh'` share. Over-specifying is sound because
     /// `M06.impl_frame` frames each branch to it, and the case's own signature
     /// is then composed row-polymorphically like anything else.
     | StCase bs ->
       (match sh with
        | [] -> Inl "if: the stack is empty; the condition must leave a bool"
        | s :: sr ->
          if s.sl_ty <> TPrim PBool
          then Inl "if: the condition must leave a bool on top of the stack"
          else if length bs <> 2
          then Inl "if: a bool has exactly two branches"
          else (match elab_branches env cs (base + 3) sr None [] [] bs with
                | Inl e -> Inl e
                | Inr (sh', bts, dacc') ->
                  (match bts with
                   /// Matched rather than indexed: `length bs = 2` was checked
                   /// above but does not travel in `elab_branches`' type, and a
                   /// refinement there would be carried for one caller.
                   | [b0; b1] ->
                     let o0 : op_id = base + 1 in
                     let o1 : op_id = base + 2 in
                     let odecl : op_decl =
                       { od_eff = eff_case; od_stage = SStatic;
                         od_sig = { op_pre  = slot_tys sr
                                  ; op_post = slot_tys sh' } } in
                     elab_terms env cs (base + sterm_size t) sh'
                       (THandle eff_case [] TNil [(o0, b0); (o1, b1)]
                          (TDispatch [o0; o1] bool_variants)
                        :: TPrimOp PBoolSum :: acc)
                       (GOp o0 odecl :: GOp o1 odecl :: (dacc' @ dacc)) rest
                   | _ -> Inl "if: expected exactly two branches")))

     /// The handler's own parts are elaborated against stacks that are fully
     /// known before the body is looked at — the state comes from `over ( … )`
     /// and each operation's arguments from its declaration — so they need no
     /// information from the surrounding program. Only the body runs on the
     /// enclosing stack.
     ///
     /// The exit shape is the state ON TOP of whatever the body left (D-46,
     /// D-47), mirroring `M06`'s rule, which re-derives it independently.
     | StHandle ename sttys init impls body ->
       (match elab_handle_parts env (base + 1) ename sttys init impls with
        | Inl e -> Inl e
        | Inr (eid, st, it, ims, d1) ->
          (match elab_terms env cs (base + 1 + sterms_size init) sh [] [] body with
           | Inl e -> Inl e
           | Inr (shb, bts, d2) ->
             elab_terms env cs (base + sterm_size t) (anon_slots st @ shb)
               (THandle eid st it ims (seq_of bts) :: acc) (d1 @ d2 @ dacc) rest))

     /// `with` IS A DICTIONARY HANDLER (D-76). It elaborates to
     ///
     ///     THandle eff_dict [] TNil [(old, TWord new); …] body
     ///
     /// and nothing else. `E06` then discharges that frame statically, which is
     /// `M11.specialize` restricted to one effect — so `with` costs nothing at
     /// runtime for the reason D04 gives rather than because the elaborator has
     /// a rewrite rule for it.
     ///
     /// WHAT THIS REPLACED, and why it was wrong. The old case emitted
     /// `subst_words ids body`: a rename of the calls the block writes. That is
     /// NOT what handling the Dictionary effect means, and D-75 produced the
     /// counterexample — `with { greet bye } { shout }` left `greet` alone
     /// inside `shout`, while `handle Dict { greet { bye } } { shout }` rebound
     /// it. Two spellings of one construct disagreeing on a result is precisely
     /// what D-02 says cannot happen, so the substitution had to go.
     ///
     /// The body is still elaborated under the ORIGINAL names, which keeps the
     /// shape model the one the reader wrote. What licenses that is no longer an
     /// equality check here but `M06.infer_impls`, which types each replacement
     /// at the operation's declared signature — the same rule every other
     /// handler obeys, and weaker than equality in exactly the way `impl_frame`
     /// is (D-68).
     | StWith su body ->
       (match resolve_rebinds env su with
        | Inl e -> Inl e
        | Inr ids ->
          (match elab_terms env cs (base + 1) sh [] [] body with
           | Inl e -> Inl e
           | Inr (shb, bts, d1) ->
             elab_terms env cs (base + sterm_size t) shb
               (THandle eff_dict_r [] TNil (rebind_impls ids) (seq_of bts)
                :: acc)
               (d1 @ dacc) rest))

     /// `try { … } catch { … }` (D-71).
     ///
     /// BOTH BLOCKS ARE ELABORATED AGAINST `[]`, and that is the one place this
     /// case makes a choice. `M05.TTry` records the body's `pre` so `R02` knows
     /// how far to cut the stack back on an abort, and the shape model cannot
     /// supply it: the model is one concrete stack, so it says what the body
     /// LEFT and not how deep the body reached. `StCase` over-approximates its
     /// declarations to the full modelled shape and is safe doing so because
     /// `M06.impl_frame` frames the branches back down; here the same
     /// over-approximation would mean an abort discards the caller's whole
     /// stack and `catch` has to rebuild it. Giving the body an empty entry
     /// shape instead makes `pre = []` true by construction, and a body that
     /// reaches out gets "the stack is empty" rather than a wrong answer.
     ///
     /// The two blocks must agree on their exit shape, for the same reason two
     /// branches of a `case` must: one of them runs and the following code
     /// cannot know which. `M06.infer` re-derives the agreement independently.
     /// NAMED LOCALS ARE COPIED IN (D-87). The block still runs on its own
     /// stack — that part is forced, for the reason above — but "its own stack"
     /// need not be empty. Each local the block READS is picked to the top
     /// first, and the block is elaborated against exactly those copies, so
     /// `pre` stays known by construction while `try { $n validate }` means what
     /// it looks like it means.
     ///
     /// Copies, not moves, and always: an abort cuts the stack back past them,
     /// so a moved local would be destroyed on a path the reader did not write.
     /// `drop_named` clears any copy a repeated read left behind, exactly as it
     /// does at the end of a body — without it the block's exit shape would
     /// carry the leftover and stop agreeing with `catch`.
     ///
     /// THE CATCH BLOCK GETS NOTHING, and that is not an oversight of this case
     /// but `M06`'s rule: `catch` is typed at `pre = []` because `R02` restores
     /// the stack BELOW the body's inputs, so there is nowhere for a copy to
     /// survive. Giving `catch` access is a core change and it is the same
     /// change Q-17 wants — see N02 Q-22.
     | StTry btry bcatch ->
       (match copy_locals sh [] [] (mentioned_locals sh [] btry) with
        | Inl e -> Inl e
        | Inr (blk, hoist) ->
          (match elab_terms env cs (base + 1) blk [] [] btry with
           | Inl e -> Inl e
           | Inr (shb0, bts0, d1) ->
             (match drop_named (length shb0) shb0 [] with
              | Inl e -> Inl e
              | Inr (shb, bts1) ->
                (match mentioned_locals sh [] bcatch with
                 /// Reported here rather than left to surface as "unbound local"
                 /// from the catch block's own elaboration, because the two are
                 /// different mistakes: one is a typo, this one is a rule.
                 | x :: _ ->
                   Inl ("$" ^ x ^ " is not in scope in a catch block: an abort \
                        cuts the stack back before catch runs, so it receives \
                        nothing. Read the local in the try block instead")
                 | [] ->
                (match elab_terms env cs (base + 1 + sterms_size btry) [] [] [] bcatch with
                 | Inl e -> Inl e
                 | Inr (shc, cts, d2) ->
                   if slot_tys shc <> slot_tys shb
                   then Inl "try: the catch block must leave the same stack as \
                             the try block"
                   else elab_terms env cs (base + sterm_size t) (shb @ sh)
                          (TTry eff_fail (slot_tys blk)
                                (seq_of (bts0 @ bts1)) (seq_of cts)
                           :: (hoist @ acc))
                          (d1 @ d2 @ dacc) rest))))))

/// Elaborate each branch against the SAME entry shape and require them to
/// agree on the exit shape.
///
/// Agreement is equality of the modelled shape, which is stricter-looking than
/// `M06.srow_join` but means the same thing here: the model is one concrete
/// stack, so a branch reaching further beneath it simply leaves a shorter
/// list, and two branches agree exactly when those lists coincide. M06 then
/// re-derives the same fact row-polymorphically and independently.
and elab_branches (env:nenv) (cs:counts) (base:nat) (sh0:shape)
                  (expect:option shape) (acc:list term)
                  (dacc:list gdecl) (bs:list (list sterm))
  : Tot (either string (shape & list term & list gdecl))
        (decreases %[sterm_lists_size bs; 1]) =
  match bs with
  | [] -> (match expect with
           | None    -> Inl "if: no branches"
           | Some sh -> Inr (sh, rev acc, dacc))
  | b :: r ->
    (match elab_terms env cs base sh0 [] [] b with
     | Inl e -> Inl e
     | Inr (sh1, ts, d1) ->
       let ok = (match expect with None -> true | Some ex -> ex = sh1) in
       if not ok
       then Inl "the branches of an if leave the stack in different states"
       else elab_branches env cs (base + sterms_size b) sh0 (Some sh1)
              (seq_of ts :: acc) (d1 @ dacc) r)

/// Resolve a `handle`'s effect, state, initialiser and implementations.
///
/// Shared by BOTH passes, which is why it is here rather than inlined: none of
/// these parts depends on the surrounding stack, so signature inference can
/// check them exactly as the main pass does and only has to model the body.
///
/// Locals are deliberately out of scope inside `init` and the implementations
/// — they run on the handler's stacks, not the definition's — which falls out
/// of passing an empty shape and empty counts, and is why `E02.count_var` does
/// not look inside either.
and elab_handle_parts (env:nenv) (base:nat) (ename:string) (sttys:list sty)
                      (init:list sterm) (impls:list (string & list sterm))
  : Tot (either string (eff_id & seg & term & list (op_id & term)
                        & list gdecl))
        (decreases %[(sterms_size init + simpls_size impls <: nat); 2]) =
  match lookup_eff env ename with
  | None -> Inl ("unknown effect: " ^ ename)
  | Some eid ->
    (match elab_tys env.ne_types sttys with
     | Inl e -> Inl e
     /// THE REVERSAL again: `over ( a b )` reads bottom-to-top, the core wants
     /// head = top.
     | Inr ds ->
       let st = rev ds in
       (match elab_terms env [] base [] [] [] init with
        | Inl e -> Inl e
        | Inr (shi, its, d1) ->
          if shi <> anon_slots st
          then Inl ("handle " ^ ename
                    ^ ": init must leave exactly the state declared by over ( … )")
          else (match elab_impls env (base + sterms_size init) eid st [] [] impls with
                | Inl e   -> Inl e
                | Inr (ims, d2) -> Inr (eid, st, seq_of its, ims, d1 @ d2))))

/// One implementation per operation, each checked at `st @ op_pre -- st @
/// op_post` — the operation's declared signature with the state framed on top.
///
/// An operation of the effect that is NOT implemented here is not an error: it
/// forwards to the next handler outward, which is what makes partial overriding
/// of a Dictionary possible (D04). What is an error is implementing something
/// that is not an operation of this effect.
and elab_impls (env:nenv) (base:nat) (eid:eff_id) (st:seg) (acc:list (op_id & term))
               (dacc:list gdecl) (im:list (string & list sterm))
  : Tot (either string (list (op_id & term) & list gdecl))
        (decreases %[simpls_size im; 1]) =
  match im with
  | [] -> Inr (rev acc, dacc)
  | (opname, blk) :: r ->
    (match lookup_name env opname with
     | None -> Inl ("unknown operation: " ^ opname)
     | Some n ->
       /// EVERY WORD IS AN OPERATION OF `Dict` (D-63, D-75). `n_op` is `None`
       /// for an ordinary definition, and that used to be read as "not an
       /// operation at all" — which contradicted the table D-63 built, where a
       /// `define` gets an `op_decl` under `eff_dict` exactly as a `declare`
       /// gets one under its own effect. Defaulting it here is what lets
       /// `handle Dict { foo { … } } { … }` rebind a word for the extent of a
       /// block, which is the surface half of the runtime path `R02` now walks.
       let e' = (match n.n_op with Some e -> e | None -> eff_dict_r) in
       if e' <> eid
       then Inl (opname ^ " is not an operation of this effect")
       else
         let entry = anon_slots st @ anon_slots n.n_sig.pre in
         let ex    = anon_slots st @ anon_slots n.n_sig.post in
         (match elab_terms env [] base entry [] [] blk with
          | Inl e -> Inl e
          | Inr (sh2, ts, d1) ->
            if sh2 <> ex
            then Inl (opname ^ ": an implementation must leave the handler's \
                                state on top of the operation's results")
            else elab_impls env (base + sterms_size blk) eid st
                   ((n.n_id, seq_of ts) :: acc) (d1 @ dacc) r))

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
     | StStr _ -> infer_terms env cs (ipush (MT (TPrim PStr)) st) rest

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

     /// An explicit instantiation needs no stack model to resolve, which is
     /// exactly what makes it usable here (D-82): this pass runs BEFORE any
     /// signature is known and works with metavariables, so `match_ty` — which
     /// needs a concrete `M01.dtype` to match against — has nothing to bite on.
     /// Written types sidestep that, so `define f { g[i64] }` infers.
     | StWordAt w tys ->
       (match lookup_gen_in env.ne_gens w with
        | None -> Inl (w ^ " is not generic, so it takes no type arguments")
        | Some g ->
          if length g.g_params <> length tys
          then Inl (w ^ " has " ^ string_of_int (length g.g_params)
                    ^ " type parameters but was given "
                    ^ string_of_int (length tys))
          else
            (match explicit_sub env.ne_types g.g_params tys with
             | Inl e   -> Inl (w ^ ": " ^ e)
             | Inr su ->
               (match elab_sig env.ne_types (subst_ssig su g.g_sig) with
                | Inl e   -> Inl (w ^ ": " ^ e)
                | Inr row ->
                  (match iapply_pre w st row.pre with
                   | Inl e   -> Inl e
                   | Inr st1 -> infer_terms env cs (ipush_post row.post st1) rest))))

     | StWord w ->
       (match lookup_gen_in env.ne_gens w with
        /// The implicit form is the one case this pass cannot serve, and the
        /// message says what to write instead rather than reporting the word
        /// missing. Matching needs concrete types; a body with no written
        /// signature has metavariables where they would be.
        | Some _ ->
          Inl (w ^ " is generic; in a definition with no written signature, \
                instantiate it explicitly, as in " ^ w ^ "[i64]")
        | None ->
       (match lookup_name env w with
        | None -> Inl ("unknown word: " ^ w)
        | Some n ->
          (match iapply_pre w st n.n_sig.pre with
           | Inl e   -> Inl e
           | Inr st1 -> infer_terms env cs (ipush_post n.n_sig.post st1) rest)))

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
                | Inr st3 -> infer_terms env cs st3 rest))

     /// Nothing here needs a metavariable. The state comes from `over ( … )`
     /// and every implementation runs on a stack built from it and the
     /// operation's declaration, so `elab_handle_parts` — the concrete pass —
     /// checks them unchanged, and only the body is modelled.
     ///
     /// The elaborated terms it returns are thrown away and rebuilt in pass 2.
     /// That is the same duplication `infer_terms` accepts everywhere else, and
     /// it is what keeps the two passes independent rather than one threading
     /// half-built output through the other.
     | StHandle ename sttys init impls body ->
       (match elab_handle_parts env 0 ename sttys init impls with
        | Inl e -> Inl e
        | Inr (_, stseg, _, _, _) ->
          (match infer_terms env cs st body with
           | Inl e    -> Inl e
           | Inr stb  -> infer_terms env cs (ipush_post stseg stb) rest))

     /// A `with` is invisible to this pass by construction: the rebindings are
     /// required to have equal signatures, so the body models identically
     /// whether or not it is substituted. The resolution still runs, so an
     /// unknown or mismatched name is reported here too rather than only in
     /// pass 2.
     | StWith su body ->
       (match resolve_rebinds env su with
        | Inl e -> Inl e
        | Inr _ ->
          (match infer_terms env cs st body with
           | Inl e   -> Inl e
           | Inr st' -> infer_terms env cs st' rest))

     /// NO METAVARIABLE CAN ESCAPE A `try` (D-71), because neither block runs
     /// on the enclosing stack — the same reason a handler's initialiser and
     /// implementations are checked by the concrete pass here rather than
     /// modelled. So both blocks go through `elab_terms` at an empty entry
     /// shape, exactly as pass 2 will run them, and all this pass takes back is
     /// what they leave behind.
     | StTry btry bcatch ->
       (match elab_terms env cs 0 [] [] [] btry with
        | Inl e -> Inl e
        | Inr (shb, _, _) ->
          (match elab_terms env cs 0 [] [] [] bcatch with
           | Inl e -> Inl e
           | Inr (shc, _, _) ->
             if slot_tys shc <> slot_tys shb
             then Inl "try: the catch block must leave the same stack as the \
                       try block"
             else infer_terms env cs (ipush_post (slot_tys shb) st) rest)))

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
let elab_define (env:nenv) (base:nat) (sg:ssig) (body:list sterm)
  : Tot (either string (srow & term & list gdecl)) =
  match elab_sig env.ne_types sg with
  | Inl e -> Inl e
  | Inr row ->
    let sh0 = entry_shape (rev sg.ss_in) row.pre in
    let cs  = build_counts sg.ss_in body in
    (match elab_terms env cs base sh0 [] [] body with
     | Inl e -> Inl e
     | Inr (sh1, ts1, ds) ->
       (match drop_named (length sh1) sh1 [] with
        | Inl e -> Inl e
        | Inr (_, ts2) -> Inr (row, seq_of (ts1 @ ts2), ds)))

/// Elaborate a definition with no written signature: infer one, then elaborate
/// the body against it with the ordinary concrete pass. There are no named
/// parameters in this form — naming happens in a signature — so the entry shape
/// is anonymous and no end-of-body drop is needed.
let elab_define_infer (env:nenv) (base:nat) (body:list sterm)
  : Tot (either string (srow & term & list gdecl)) =
  match infer_sig env body with
  | Inl e -> Inl e
  | Inr row ->
    (match elab_terms env [] base (anon_slots row.pre) [] [] body with
     | Inl e           -> Inl e
     | Inr (_, ts, ds) -> Inr (row, seq_of ts, ds))

/// Elaborate a bare expression against a known incoming stack shape.
let elab_expr (env:nenv) (base:nat) (incoming:list dtype) (body:list sterm)
  : Tot (either string (term & list gdecl)) =
  match elab_terms env [] base (anon_slots incoming) [] [] body with
  | Inl e            -> Inl e
  | Inr (_, ts, ds)  -> Inr (seq_of ts, ds)
