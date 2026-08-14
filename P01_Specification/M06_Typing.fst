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

/// ONE TABLE OF SIGNATURES, NOT TWO (D-63).
///
/// This record used to carry `w_defs : list (word_id & wdecl)` giving each word
/// a signature and a row, ALONGSIDE `w_ops` giving each operation an effect and
/// a signature. Nothing related them, and nothing had to until M07 had to denote
/// `TWord w`: a word call is an operation call (D-60), so `M04.Op` demands
/// arguments of shape `(op_of w).op_pre` where the signature says
/// `(w_sig w).pre`. M07 stated the missing agreement as a predicate `coherent`
/// and refined `denote_static` by it — and P03 did not satisfy it, so the
/// denotation was vacuous for every program the REPL could actually elaborate.
///
/// The fix is not to make P03 maintain the agreement. It is to remove the
/// second copy: `w_sig` now READS FROM `w_ops`, so the two cannot disagree
/// because there is only one of them, `coherent` is definitionally true and has
/// been deleted from M07, and a word with no `w_ops` entry has no signature
/// rather than a stale one. A discipline P03 could forget becomes an
/// impossibility.
///
/// What is left here is the part `w_ops` genuinely does not know: the effects a
/// word's BODY performs, which is not a property of its declaration. The
/// Dictionary entry itself is derived, not stored — see `w_eff`.
///
/// AN ASSOCIATION LIST, for the reason given at `M04.sig_env` (D-45): a
/// function-typed field cannot be built without a closure, and P03's REPL has
/// to build one of these for every line it checks.
type wenv = {
  /// The extra effects each word's body performs, beyond performing itself.
  w_effs : list (word_id & erow);
  /// Every word's signature and effect, operations and Dictionary words alike.
  w_ops  : sig_env;
}

let rec lookup_row (ds:list (word_id & erow)) (w:word_id)
  : Tot erow (decreases ds) =
  match ds with
  | []            -> pure_row
  | (w', e) :: r  -> if w' = w then e else lookup_row r w

/// A word's signature IS its operation's signature. An UNDECLARED word gets
/// `M04.op_unknown`, hence `( -- )`: `infer` then reports it by way of the
/// composition failing, which gives a signature mismatch at the point of use
/// rather than a lookup failure with no context.
let w_sig (env:wenv) (w:word_id) : Tot srow = sig_of_op (op_of env.w_ops w)

/// A word's effect row: the effect it performs BY BEING CALLED, followed by
/// whatever its body performs.
///
/// THE HEAD ENTRY IS WHAT MAKES M07's T5 TRUE (D-63). `TWord w` denotes
/// `Op w`, so `M04.within` demands `eff_of w` appear in the row; deriving that
/// entry here rather than trusting a stored one means it cannot be absent. For
/// a Dictionary word it is `(eff_dict, SStatic)` — the `!Dict` of D-37, finally
/// a real row entry instead of an elided convention. For a declared operation it
/// is the effect's own entry, which is what the row said before.
///
/// A consequence worth stating plainly: NOTHING THAT CALLS A WORD IS PURE, so
/// `is_pure` below now means "pure after the Dictionary is resolved" for exactly
/// the programs it used to call pure outright. That is not a regression, it is
/// D-37 being honest — and it is precisely the property M11's E3 claims
/// `specialize` restores.
let w_eff (env:wenv) (w:word_id) : Tot erow =
  (eff_of env.w_ops w, stage_of env.w_ops w) :: lookup_row env.w_effs w

/// A row as a reader should see it: the static `Dict` entry elided, because it
/// is on every word and therefore tells a reader nothing (D-37). Rendering and
/// the REPL's declared-effects check both go through this, so "never written"
/// is implemented in one place rather than assumed in several.
let row_visible (row:erow) : erow =
  filter (fun (e, s) -> not (e = eff_dict && s = SStatic)) row

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
(* The primitive table                                                      *)
(* ------------------------------------------------------------------------ *)

/// The typing rule for every intrinsic, as a table (D-55).
///
/// `None` is "this primitive is not well typed at these arguments", and it is
/// where the capability checks live: rejecting `SDup` at a non-copyable type
/// is the whole enforcement mechanism for linearity, and there is no separate
/// linear sublanguage anywhere else in the system.
///
/// There is no `erow` in the result, and that absence is load-bearing rather
/// than an omission — see `M05.prim_op`. Every primitive is pure, so `infer`
/// pairs this with `pure_row` unconditionally and M07's T4 gets one case for
/// the whole class.
///
/// This function is total and does not recurse, which is what makes the
/// primitive case of every induction over `term` in M07 and M09 a single
/// appeal to a lemma about `prim_sig` rather than twelve separate arguments.
let prim_sig (p:prim_op) : Tot (option srow) =
  match p with
  | PLit l -> Some ({ pre = []; post = [lit_type l] })

  /// The two capability-gated shuffles. `SSwap` needs no capability because
  /// moving a value is always permitted.
  | PStack (SDup d) ->
    if copyable d then Some ({ pre = [d]; post = [d; d] }) else None
  | PStack (SPop d) ->
    if droppable d then Some ({ pre = [d]; post = [] }) else None
  | PStack (SSwap d1 d2) ->
    Some ({ pre = [d1; d2]; post = [d2; d1] })

  /// Deep access. `SPick` copies, so it is capability-gated exactly like
  /// `SDup`; `SRoll` only moves, so it is not. The `above` segment is what
  /// makes the depth explicit in the type rather than variadic.
  | PStack (SPick above d) ->
    if copyable d
    then Some ({ pre = above @ [d]; post = d :: (above @ [d]) })
    else None
  | PStack (SRoll above d) ->
    Some ({ pre = above @ [d]; post = d :: above })

  /// Sealing is where a stack segment becomes one denotable value, and where
  /// a type may narrow its capabilities (D03).
  | PPack n caps repr ->
    Some ({ pre = repr; post = [TSeal n caps repr] })
  | PUnpack n caps repr ->
    Some ({ pre = [TSeal n caps repr]; post = repr })

  | PInj variants tag ->
    if tag < length variants
    then Some ({ pre = index variants tag; post = [TSum variants] })
    else None

  /// The boolean-to-sum coercion (D-33). Fixed tags: `false` is variant 0 and
  /// `true` is variant 1.
  | PBoolSum ->
    Some ({ pre = [TPrim PBool]; post = [TSum bool_variants] })

  /// Pointers. Well-formedness is checked at the boundary: a slot's type must
  /// not be a bare incomplete type, which is what `wf` rules out.
  | PBoxNew d ->
    if wf d then Some ({ pre = [d]; post = [TBox d] }) else None
  | PBoxOpen d ->
    if wf d then Some ({ pre = [TBox d]; post = [d] }) else None

  | PRcNew d ->
    if wf d then Some ({ pre = [d]; post = [TRc d] }) else None
  /// The `Clone` interface word. Note this is NOT `SDup`: it is available at
  /// every payload type, because cloning an `Rc` bumps a count rather than
  /// copying the pointee.
  | PRcClone d ->
    if wf d then Some ({ pre = [TRc d]; post = [TRc d; TRc d] }) else None
  /// `release`, not `pop` -- `TRc` has no `CDrop`, so this word is the only
  /// way to discard a shared handle.
  | PRcDrop d ->
    if wf d then Some ({ pre = [TRc d]; post = [] }) else None
  /// Capability-gated, like `SDup`: reading a non-copyable payload out of a
  /// shared pointer would need borrowing (N02 Q-03).
  | PRcRead d ->
    if wf d && copyable d
    then Some ({ pre = [TRc d]; post = [d; TRc d] })
    else None

  /// Roll and unroll an incomplete type.
  ///
  /// LIMITATION, recorded rather than hidden: `d` is not checked against the
  /// declaration `n` names, because `wenv` carries no type-declaration table
  /// yet. So these rules accept `PRoll n d` for any well-formed `d`. Adding a
  /// `w_decl : nom_id -> dtype` field and requiring `d = w_decl n` closes it;
  /// the rest of the design is arranged so that this is the ONLY place an
  /// environment is needed for types, which is also why `prim_sig` can take no
  /// environment at all today.
  | PRoll n d ->
    if wf d then Some ({ pre = [d]; post = [TName n] }) else None
  | PUnroll n d ->
    if wf d then Some ({ pre = [TName n]; post = [d] }) else None

(* ------------------------------------------------------------------------ *)
(* Inference                                                                *)
(* ------------------------------------------------------------------------ *)

(* ------------------------------------------------------------------------ *)
(* Dispatch                                                                 *)
(* ------------------------------------------------------------------------ *)

/// `pre` with `v` stripped off the front, or `None` if it does not start with
/// `v`. `M03.unify` already walks two segments in lockstep, and a residual pair
/// with an empty first component says exactly "the second extends the first".
let strip_pre (v:seg) (pre:seg) : Tot (option seg) =
  match unify v pre with
  | Some ([], rest) -> Some rest
  | _               -> None

/// The residual a handler implementation is instantiated at, or `None` when its
/// signature cannot be framed to the declared one (D-68).
///
/// `k` is RECOVERED, not guessed: `strip_pre` reads it off the declared `pre`,
/// and the `post` check is then an equality rather than a search. Same argument
/// as `M03.srow_join` — there are no type variables here, only prefix matching,
/// so D-31's claim that the language needs no unifier survives this too.
let impl_frame (s:srow) (st:seg) (osig:op_sig) : Tot (option seg) =
  match strip_pre s.pre (st @ osig.op_pre) with
  | None   -> None
  | Some k -> if s.post @ k = st @ osig.op_post then Some k else None

/// What `impl_frame` returning `Some k` actually means, spelled as the two
/// segment equations a caller needs. `M07`'s `THandle` clause instantiates the
/// implementation's denotation at `k`, and this is what makes the resulting type
/// the declared one.
///
/// The `pre` half is `M03.lemma_unify_common` — `strip_pre` succeeds only when
/// one residual is empty, and extending each side by the other's leftover then
/// says the declared `pre` IS the body's `pre` framed by `k`. The `post` half is
/// definitional, since `impl_frame` tests it directly.
let lemma_impl_frame (s:srow) (st:seg) (osig:op_sig)
  : Lemma (requires Some? (impl_frame s st osig))
          (ensures  (let Some k = impl_frame s st osig in
                     st @ osig.op_pre  == s.pre @ k /\
                     st @ osig.op_post == s.post @ k)) =
  let decl_pre = st @ osig.op_pre in
  /// Matched rather than left to the solver: `Some? (strip_pre …)` says the
  /// FIRST residual is empty, and that fact is inside a pattern the SMT encoding
  /// does not see through on its own.
  match unify s.pre decl_pre with
  | Some ([], _) -> lemma_unify_common s.pre decl_pre; append_l_nil decl_pre
  | _            -> ()

/// Every operation of a dispatch declares the same joined behaviour beneath its
/// own variant (D-68): variant `i` is `( variants[i] @ j.pre -- j.post )`.
///
/// THIS IS WHERE `M03.srow_join` WENT. It used to compute a `case`'s type by
/// folding the branches; now the elaborator folds it to build these
/// declarations, and this function checks they agree. The information is the
/// same and the check is cheaper, because agreement is now a property of the
/// DECLARATION rather than something rediscovered at every use.
///
/// The row is collected here too, one entry per operation, so a dispatch's
/// effects are the effects of the operations it might perform — which is what
/// `M04.within` needs and what makes M07's T5 hold for this case.
let rec dispatch_ok (env:wenv) (ops:list op_id) (variants:list seg) (j:srow)
  : Tot (option erow) (decreases ops) =
  match ops, variants with
  | [], []           -> Some pure_row
  | o :: os, v :: vs ->
    let osig = op_of env.w_ops o in
    if osig.op_pre = v @ j.pre && osig.op_post = j.post
    then (match dispatch_ok env os vs j with
          | None   -> None
          | Some r -> Some (row_union [(eff_of env.w_ops o, stage_of env.w_ops o)] r))
    else None
  | _ -> None

/// The join a dispatch is at, read off its FIRST operation. There is nothing to
/// infer: the declaration already fixes it, and `dispatch_ok` then checks the
/// rest agree. Recovering `j.pre` needs the variant's length, which is why
/// `TDispatch` carries the variants alongside the operations.
let dispatch_row (env:wenv) (ops:list op_id) (variants:list seg)
  : Tot (option srow) =
  match ops, variants with
  | o :: _, v :: _ ->
    let osig = op_of env.w_ops o in
    (match strip_pre v osig.op_pre with
     | None      -> None
     | Some jpre -> Some ({ pre = jpre; post = osig.op_post }))
  | _ -> None

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

  /// Every intrinsic, in one rule. `pure_row` is unconditional because no
  /// entry of the table can perform an operation (`M05.prim_op`).
  | TPrimOp p ->
    (match prim_sig p with
     | Some s -> Some (s, pure_row)
     | None   -> None)

  /// Words and interface operations share one rule.
  | TWord w -> Some (w_sig env w, w_eff env w)

  /// Every branch consumes its own variant's payload, and all branches must
  /// agree -- but agree in the row-polymorphic sense, not by having equal
  /// signatures. See `M03.srow_join`: one branch may reach beneath the
  /// scrutinee where another does not, provided both leave the stack in the
  /// same state. The shape after a `case` still has to be static, which is
  /// why sums cannot be segments.
  ///
  /// THE BRANCHES ARE NOT HERE ANY MORE (D-68). Eliminating a sum is performing
  /// the operation its tag selects; the branches are the implementations a
  /// `THandle` supplies, so this rule reads the joined signature off the
  /// declarations rather than folding it out of branch bodies. `infer_branches`
  /// is gone and `infer_impls` does its work.
  | TDispatch ops variants ->
    if Nil? variants || length ops <> length variants then None
    else (match dispatch_row env ops variants with
          | None   -> None
          | Some j ->
            (match dispatch_ok env ops variants j with
             | None     -> None
             | Some row ->
               Some ({ pre = TSum variants :: j.pre; post = j.post }, row)))

  /// Handling discharges `eff` from the body's row and adds whatever the
  /// initialiser and the implementations themselves need.
  ///
  /// THE STATE IS THE WHOLE OF THE RULE (D-36). `init` must be exactly
  /// `( -- st )`; each implementation is checked with `st` framed on top of the
  /// operation's declared signature; and the handler leaves `st` behind when
  /// the body finishes. There is no continuation anywhere in this rule, which
  /// is the point — an implementation is an ordinary program that returns, so
  /// it is typed like one. `st = []` recovers the stateless case exactly.
  | THandle eff st init impls body ->
    (match infer env init, infer env body, infer_impls env eff st impls with
     | Some (si, ei), Some (s, row), Some hrow ->
       if si <> { pre = []; post = st } then None
       else Some ({ pre = s.pre; post = st @ s.post },
                  row_union (row_remove eff row) (row_union ei hrow))
     | _ -> None)

  /// Handling an ABORTING effect (D-71). Three conditions, and each is one of
  /// the constraints try/catch has to satisfy:
  ///
  ///   * `pre` is the body's own `pre`. Checked, not trusted — `R02` reads it
  ///     to know how far to cut the stack back on an abort, and a term that
  ///     lied about it would restore to the wrong depth.
  ///   * `catch` consumes NOTHING. On an abort the body's inputs are gone
  ///     along with everything it had built, so there is nothing for `catch`
  ///     to consume; the stack it starts from is what was below the body.
  ///     (When generics arrive this becomes "consumes the error value", and
  ///     `op_pre` stops being discarded.)
  ///   * `catch` produces the body's `post`. The two arms leave the same stack
  ///     or the construct has no signature, which is the same agreement
  ///     `srow_join` asks of the branches of a `case`.
  ///
  /// The composite's signature is the BODY's, unchanged: a try/catch is
  /// transparent to its context. Its row is the body's minus `eff`, plus
  /// whatever `catch` itself needs — `catch` runs outside the construct it
  /// belongs to, so a `fail` inside a `catch` reaches the NEXT `try` out.
  | TTry eff pre body catch ->
    (match infer env body, infer env catch with
     | Some (s, row), Some (sc, ec) ->
       if s.pre <> pre then None
       else if sc <> { pre = []; post = s.post } then None
       else Some (s, row_union (row_remove eff row) ec)
     | _ -> None)

  /// Specialization keeps the signature and drops the static effects. The
  /// same rule serves compile-time specialization and runtime JIT.
  | TSpecialize body ->
    (match infer env body with
     | Some (s, row) -> Some (s, row_dynamic row)
     | None          -> None)

/// Each implementation is checked at the operation's declared signature with
/// the handler's state segment framed ON TOP: `st @ op_pre -- st @ op_post`.
/// "State types preserved" is exactly that framing, and it is what makes the
/// state usable without any of it appearing in the effect's declaration.
///
/// The operation must belong to `eff`. It need not be the case that every
/// operation of `eff` is implemented — an unimplemented one is not an error,
/// it forwards to the next handler outward, which is what `R02.find_handler`
/// already does and what makes partial overriding of a Dictionary possible.
///
/// AN IMPLEMENTATION MAY BE MORE ROW-POLYMORPHIC THAN ITS DECLARATION (D-68).
/// The test used to be equality, which was the one place in the language where
/// a signature had to be written at a fixed depth rather than instantiated. It
/// is now `impl_frame`: the body's own signature framed by some residual `k`
/// must give the declared one, and `k` is recovered rather than guessed.
///
/// This is sound for the reason every other framing in the language is: a
/// denotation is `r:seg -> vstack (pre @ r) -> free (post @ r)`, so a body of
/// signature `s` instantiated at `k` HAS the required type on the nose. It is
/// also what makes `TDispatch` usable at all — a `case` branch that does not
/// touch the stack beneath the scrutinee has signature `( -- )`, while the
/// operation it implements is declared at the joined depth, and demanding
/// equality would reject `if { } then { pop 1 } else { … } endif`.
and infer_impls (env:wenv) (eff:eff_id) (st:seg) (impls:list (op_id & term))
  : Tot (option erow) (decreases %[impls_size impls; 1]) =
  match impls with
  | [] -> Some pure_row
  | (op, body) :: rest ->
    (match infer env body, infer_impls env eff st rest with
     | Some (s, ei), Some er ->
       let osig = op_of env.w_ops op in
       if eff_of env.w_ops op = eff && Some? (impl_frame s st osig)
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
