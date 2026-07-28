module M06_Typing

/// catcat core specification, module 06: the typing judgment.
///
/// The judgment is `env |- t : s ! row`, and it is presented algorithmically,
/// as a total inference function rather than an inductive relation. That is
/// not a shortcut: in a concatenative language type inference IS signature
/// composition, so the "algorithm" is a fold over the term with no unification
/// variables, no constraint store, and no generalization step. This is the
/// technical reason a fast, incremental language server is realistic (D01) --
/// re-checking a token means recomposing along one spine.
///
/// Compare the length of this module with the equivalent for any applicative
/// language. The whole judgment is `infer` below, and only three of its cases
/// are interesting: `TNil` is the identity, `TSeq` is composition, and
/// everything else looks up or builds a signature.

open FStar.List.Tot
open M01_Kinds
open M02_Stacks
open M03_Signatures
open M04_Effects
open M05_Terms

(* ------------------------------------------------------------------------ *)
(* Environments and effect-row operations                                   *)
(* ------------------------------------------------------------------------ *)

noeq type wenv = {
  /// Declared signature and effect row of each named word. Because interface
  /// operations and ordinary words are both `TWord`, this table is also the
  /// Dictionary as seen by the type checker (D04).
  w_sig  : word_id -> srow;
  w_eff  : word_id -> erow;
  /// Operation declarations, used to check handler implementations.
  w_ops  : sig_env;
}

/// Row union. Kept as append: deduplication is an optimisation on the
/// representation, never a semantic step, and `lemma_within_weaken` in M04 is
/// what makes that safe.
let row_union (r1 r2:erow) : erow = r1 @ r2

/// Discharge an effect. This is what a handler does to the row of its body,
/// and the reason a handled program can be pure.
let row_remove (e:eff_id) (row:erow) : erow =
  filter (fun (e', _) -> e' <> e) row

/// Keep only the effects that survive to runtime. Applied by `TSpecialize`,
/// this is the zero-cost property of D04 showing up directly in the type
/// system: a fully static row specializes to a pure program.
let row_dynamic (row:erow) : erow =
  filter (fun (_, s) -> s = SDynamic) row

(* ------------------------------------------------------------------------ *)
(* Inference                                                                *)
(* ------------------------------------------------------------------------ *)

/// Measures follow the M01/M05 pattern: rank orders `list(1) > term(0)`, and
/// every term-to-list edge strictly decreases size.
let rec infer (env:wenv) (t:term)
  : Tot (option (srow & erow)) (decreases %[(term_size t <: nat); 0]) =
  match t with
  /// Identity of the category.
  | TNil -> Some (sid, pure_row)

  /// Composition in the category. This one case is the entire sequencing
  /// story of the language.
  | TSeq a b ->
    (match infer env a, infer env b with
     | Some (sa, ea), Some (sb, eb) ->
       (match compose sa sb with
        | Some s -> Some (s, row_union ea eb)
        | None   -> None)
     | _ -> None)

  | TLit l -> Some ({ pre = []; post = [lit_type l] }, pure_row)

  /// The two capability-gated rules. Rejecting `SDup` at a non-copyable type
  /// is the whole of linearity enforcement; there is no separate linear
  /// sublanguage.
  | TStack (SDup d) ->
    if copyable d then Some ({ pre = [d]; post = [d; d] }, pure_row) else None
  | TStack (SPop d) ->
    if droppable d then Some ({ pre = [d]; post = [] }, pure_row) else None
  | TStack (SSwap d1 d2) ->
    Some ({ pre = [d1; d2]; post = [d2; d1] }, pure_row)

  /// Deep access. `SPick` copies, so it is capability-gated exactly like
  /// `SDup`; `SRoll` only moves, so it is not. The `above` segment is what
  /// makes the depth explicit in the type rather than variadic.
  | TStack (SPick above d) ->
    if copyable d
    then Some ({ pre = above @ [d]; post = d :: (above @ [d]) }, pure_row)
    else None
  | TStack (SRoll above d) ->
    Some ({ pre = above @ [d]; post = d :: above }, pure_row)

  /// Words and interface operations share one rule.
  | TWord w -> Some (env.w_sig w, env.w_eff w)

  /// Sealing is where a stack segment becomes one denotable value, and where
  /// a type may narrow its capabilities (D03).
  | TPack n caps repr ->
    Some ({ pre = repr; post = [TSeal n caps repr] }, pure_row)
  | TUnpack n caps repr ->
    Some ({ pre = [TSeal n caps repr]; post = repr }, pure_row)

  | TInj variants tag ->
    if tag < length variants
    then Some ({ pre = index variants tag; post = [TSum variants] }, pure_row)
    else None

  /// The boolean-to-sum coercion (D-33). Fixed tags: `false` is variant 0 and
  /// `true` is variant 1.
  | TBoolSum ->
    Some ({ pre = [TPrim PBool]; post = [TSum bool_variants] }, pure_row)

  /// Every branch consumes its own variant's payload, and all branches must
  /// agree -- but agree in the row-polymorphic sense, not by having equal
  /// signatures. See `M03.srow_join`: one branch may reach beneath the
  /// scrutinee where another does not, provided both leave the stack in the
  /// same state. The shape after a `case` still has to be static, which is
  /// why sums cannot be segments.
  ///
  /// A branch's arm is its body run after its payload has been pushed, so the
  /// arm is `compose (push variant_i) branch_i`. Joining the arms gives what
  /// the whole `case` demands beneath the scrutinee and leaves behind.
  | TCase variants branches ->
    if Nil? variants || length branches <> length variants then None
    else (match infer_branches env variants branches with
          | Some (j, row) ->
            Some ({ pre = TSum variants :: j.pre; post = j.post }, row)
          | None -> None)

  /// Handling discharges `eff` from the body's row and adds whatever the
  /// implementations themselves need.
  ///
  /// NOTE: implementations are checked against the operation's declared
  /// signature, which is the correct rule for interface/class methods and for
  /// any handler that resumes exactly once. Handlers that capture and reuse
  /// the continuation explicitly need the continuation in their signature;
  /// that refinement belongs with the deep-handler semantics in M10 and is
  /// deliberately not attempted here.
  | THandle eff impls body ->
    (match infer env body, infer_impls env eff impls with
     | Some (s, row), Some hrow ->
       Some (s, row_union (row_remove eff row) hrow)
     | _ -> None)

  /// Specialization keeps the signature and drops the static effects. The
  /// same rule serves compile-time specialization and runtime JIT.
  | TSpecialize body ->
    (match infer env body with
     | Some (s, row) -> Some (s, row_dynamic row)
     | None          -> None)

  /// Pointers. Well-formedness is checked at the boundary: a slot's type must
  /// not be a bare incomplete type, which is what `wf` rules out.
  | TBoxNew d ->
    if wf d then Some ({ pre = [d]; post = [TBox d] }, pure_row) else None
  | TBoxOpen d ->
    if wf d then Some ({ pre = [TBox d]; post = [d] }, pure_row) else None

  | TRcNew d ->
    if wf d then Some ({ pre = [d]; post = [TRc d] }, pure_row) else None
  /// The `Clone` interface word. Note this is NOT `SDup`: it is available at
  /// every payload type, because cloning an `Rc` bumps a count rather than
  /// copying the pointee.
  | TRcClone d ->
    if wf d then Some ({ pre = [TRc d]; post = [TRc d; TRc d] }, pure_row)
    else None
  /// `release`, not `pop` -- `TRc` has no `CDrop`, so this word is the only
  /// way to discard a shared handle.
  | TRcDrop d ->
    if wf d then Some ({ pre = [TRc d]; post = [] }, pure_row) else None
  /// Capability-gated, like `SDup`: reading a non-copyable payload out of a
  /// shared pointer would need borrowing (N02 Q-03).
  | TRcRead d ->
    if wf d && copyable d
    then Some ({ pre = [TRc d]; post = [d; TRc d] }, pure_row)
    else None

  /// Roll and unroll an incomplete type.
  ///
  /// LIMITATION, recorded rather than hidden: `d` is not checked against the
  /// declaration `n` names, because `wenv` carries no type-declaration table
  /// yet. So these rules accept `TRoll n d` for any `d`. Adding a `w_decl :
  /// nom_id -> dtype` field and requiring `d = w_decl n` closes it; the rest of
  /// the design is arranged so that this is the ONLY place an environment is
  /// needed for types.
  | TRoll n d ->
    if wf d then Some ({ pre = [d]; post = [TName n] }, pure_row) else None
  | TUnroll n d ->
    if wf d then Some ({ pre = [TName n]; post = [d] }, pure_row) else None

/// The arm of one branch: push its variant's payload, then run the branch.
/// Partial for the same reason `compose` is -- the branch may want a shape the
/// payload does not supply.
and infer_branches (env:wenv) (variants:list seg) (branches:list term)
  : Tot (option (srow & erow)) (decreases %[terms_size branches; 1]) =
  match variants, branches with
  | [v], [b] ->
    (match infer env b with
     | Some (s, e) -> (match compose ({ pre = []; post = v }) s with
                       | Some arm -> Some (arm, e)
                       | None     -> None)
     | None        -> None)
  | v :: vs, b :: bs ->
    (match infer env b, infer_branches env vs bs with
     | Some (s, e), Some (j, e') ->
       (match compose ({ pre = []; post = v }) s with
        | None     -> None
        | Some arm -> (match srow_join arm j with
                       | Some j' -> Some (j', row_union e e')
                       | None    -> None))
     | _ -> None)
  | _ -> None

and infer_impls (env:wenv) (eff:eff_id) (impls:list (op_id & term))
  : Tot (option erow) (decreases %[impls_size impls; 1]) =
  match impls with
  | [] -> Some pure_row
  | (op, body) :: rest ->
    (match infer env body, infer_impls env eff rest with
     | Some (s, ei), Some er ->
       let osig = env.w_ops.op_of op in
       if env.w_ops.eff_of op = eff
          && s.pre = osig.op_pre
          && s.post = osig.op_post
       then Some (row_union ei er)
       else None
     | _ -> None)

(* ------------------------------------------------------------------------ *)
(* Derived predicates                                                       *)
(* ------------------------------------------------------------------------ *)

let well_typed (env:wenv) (t:term) : bool = Some? (infer env t)

/// A pure program: well typed with an empty effect row. `Pure` here is the
/// real thing, not a convention -- M07 gives such a program a denotation with
/// no `Op` nodes at all.
let is_pure (env:wenv) (t:term) : bool =
  match infer env t with
  | Some (_, row) -> Nil? row
  | None          -> false

(* ------------------------------------------------------------------------ *)
(* Facts about the judgment                                                 *)
(* ------------------------------------------------------------------------ *)

/// The empty program is the identity, and sequencing with it changes nothing.
/// Together with `M03.lemma_compose_assoc` this is what makes the source-level
/// claim "juxtaposition is associative with unit" a theorem rather than a
/// convention -- programmers rely on it every time they factor a definition.
let lemma_infer_nil (env:wenv)
  : Lemma (infer env TNil == Some (sid, pure_row)) = ()

let lemma_infer_seq_nil_left (env:wenv) (t:term)
  : Lemma (requires Some? (infer env t))
          (ensures (let Some (s, row) = infer env t in
                    infer env (TSeq TNil t) == Some (s, row))) =
  let Some (s, _) = infer env t in
  lemma_compose_left_unit s

let rec lemma_eff_mem_dynamic (row:erow) (e:eff_id)
  : Lemma (ensures eff_mem e (row_dynamic row) ==> eff_mem e row)
          (decreases row) =
  match row with
  | []     -> ()
  | _ :: r -> lemma_eff_mem_dynamic r e

/// Specialization never introduces effects: the row of a specialized program
/// is contained in the row of the original. This is the type-level half of
/// D04's zero-cost claim; M11 supplies the semantic half.
let lemma_specialize_row_shrinks (env:wenv) (t:term)
  : Lemma (requires Some? (infer env (TSpecialize t)))
          (ensures (let Some (_, row')  = infer env (TSpecialize t) in
                    let Some (_, row)   = infer env t in
                    forall e. eff_mem e row' ==> eff_mem e row)) =
  let Some (_, row) = infer env t in
  FStar.Classical.forall_intro (lemma_eff_mem_dynamic row)

/// If every entry of a row is static, filtering for dynamic entries leaves
/// nothing.
let rec filter_all_static (row:erow)
  : Lemma (requires all_static row)
          (ensures Nil? (row_dynamic row))
          (decreases row) =
  match row with
  | []           -> ()
  | (_, _) :: r  -> filter_all_static r

/// A fully static row specializes away entirely: the residual program is
/// pure. This is the statement that a compile-time-only abstraction costs
/// nothing at runtime, and it is the property the object model, the module
/// system and monomorphised generics all rely on.
let lemma_static_specializes_to_pure (env:wenv) (t:term)
  : Lemma (requires (match infer env t with
                     | Some (_, row) -> all_static row
                     | None          -> False))
          (ensures (match infer env (TSpecialize t) with
                    | Some (_, row') -> Nil? row'
                    | None           -> False)) =
  let Some (_, row) = infer env t in
  filter_all_static row
