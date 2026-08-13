module M07_Denotation

/// catcat core specification, module 07: denotational semantics.
///
/// A well-typed program denotes a row-polymorphic, effectful stack
/// transformer. Sequencing denotes Kleisli composition in the free monad, so
/// the draft's claim that "a program is a complete composition of functions,
/// without reference to data" stops being a slogan and becomes the *definition*
/// of the `TSeq` clause below.
///
/// THE DESIGN DECISION THIS MODULE RESTS ON is in `cdenote`: the row is an index
/// of the TYPE, rather than a property of a single function refined by a
/// statement about `r`. That makes framing definitional instead of a proof
/// obligation discharged at every word, which is what lets `dcompose` exist as a
/// combinator at all, which is in turn what makes T2 hold by construction.
///
/// WHAT "BY CONSTRUCTION" DOES AND DOES NOT MEAN, since T2 is the claim a reader
/// will check first. The content did not vanish; it MOVED, and it moved into
/// M03. `dcompose` does not prove that `M03.compose` computes the right
/// signature -- it ASSUMES it, via a `squash` of the `unify` equation, and
/// discharges the resulting segment arithmetic using `M03.lemma_unify_common`
/// and `lemma_unify_disjoint`. Those are proved, so the composite claim stands;
/// but the theorem that sequencing is Kleisli composition is now
/// `M03.lemma_compose_assoc` plus the `unify` lemmas plus a definition, rather
/// than an induction over `term` in this file. What is genuinely gained is that
/// no case of `denote_static` can get composition wrong, because there is only
/// one place composition is written.
///
/// STATUS: `denote_static` is DEFINED, for the whole core except `TSpecialize`
/// (D-61) and `PUnroll` (D-62). NO ADMITS. Both exclusions are preconditions
/// discharged by `false_elim`, but they are not the same kind of thing:
/// `TSpecialize`'s meaning is M11's E2, which is stated against this function,
/// so defining it here would be circular -- a permanent boundary. `PUnroll` has
/// no meaning as `M06.prim_sig` types it, because writing the denotation is what
/// exposed a genuine soundness hole in the roll/unroll rules (see `prim_den` and
/// N02 Q-13) -- a temporary defect marker that gets deleted, not discharged.
///
/// THREE THINGS FELL OUT OF WRITING THIS, none of which was visible from the
/// typing rules alone. They are the reason a denotation is worth having even
/// before any theorem is proved about it:
///
///   1. `TWord w` denotes `Op w` -- a word call and an operation call are the
///      SAME node of the free monad. That is D-37 and D-01 made semantic (D-60).
///   2. `wenv`'s two signature tables had to agree, and nothing made them. Stating
///      the agreement as a side condition here was the wrong repair, because P03
///      did not satisfy it; M06 now has ONE table and the agreement is
///      definitional (D-63). See the note where `coherent` used to be.
///   3. T5 was FALSE as stated, because a plain word's denotation performs an
///      operation its row does not mention. `!Dict` is now a reserved effect id
///      (`M04.eff_dict`) that `M06.w_eff` derives, so T5 is true again as
///      originally written. See the restatement at the foot of this file.
///
/// Points 2 and 3 turned out to be one change, which is the useful part: the
/// same edit that makes the semantics non-vacuous for real environments also
/// repairs the soundness statement.

open FStar.List.Tot
open FStar.FunctionalExtensionality
open M01_Kinds
open M02_Stacks
open M03_Signatures
open M04_Effects
open M05_Terms
open M06_Typing

(* ------------------------------------------------------------------------ *)
(* What a program means                                                     *)
(* ------------------------------------------------------------------------ *)

/// A denotation is indexed by the row `r`, rather than being a single function
/// refined by a property mentioning `r`. This is the whole difference from the
/// abandoned draft: quantifying over the row in the TYPE means framing is
/// available definitionally instead of as a proof obligation at every word.
type cdenote (env:sig_env) (s:srow) =
  r:seg -> vstack (s.pre @ r) -> free env (s.post @ r)

/// The empty program denotes the identity, at every row.
let dnil (env:sig_env) : cdenote env sid =
  fun _ stk -> Pure stk

/// A pure, shape-specific transformer lifted to a denotation. `M02.frame` does
/// the work and `M02.lemma_frame_apply` is its correctness statement.
let dpure (env:sig_env) (s:srow) (f:xform s.pre s.post) : cdenote env s =
  fun r stk -> Pure (frame r f stk)

(* ------------------------------------------------------------------------ *)
(* Transport                                                                *)
(* ------------------------------------------------------------------------ *)

/// Reassociation of `@` is the only transport this module needs, and it needs it
/// constantly: every combinator below instantiates a denotation's implicit row
/// at `extra @ r` and must then see `(x @ extra) @ r` and `x @ (extra @ r)` as
/// the same stack shape. The equalities are propositional, so each site calls
/// `append_assoc` and lets the indices be identified by the solver.
///
/// Framing a denotation by a fixed extra segment. This is `M02.frame` one level
/// up -- there it framed a shape-specific transformer, here it re-indexes an
/// already row-polymorphic one -- and it is what makes a `case` branch that
/// reaches deeper than its siblings usable at the joined signature (`M03.srow_join`).
let dframe (env:sig_env) (a:srow) (extra:seg) (f:cdenote env a)
  : cdenote env ({ pre = a.pre @ extra; post = a.post @ extra }) =
  fun r stk ->
    append_assoc a.pre extra r;
    append_assoc a.post extra r;
    f (extra @ r) stk

(* ------------------------------------------------------------------------ *)
(* T2: sequencing IS Kleisli composition                                    *)
(* ------------------------------------------------------------------------ *)

/// Composition of denotations along `M03.compose`, residuals and all.
///
/// THIS IS T2, and stating it as a combinator rather than as a lemma is the
/// point: `denote_static`'s `TSeq` clause is a call to this function, so
/// "juxtaposition denotes Kleisli composition" is not something proved about the
/// denotation afterwards, it is how the denotation is built. There is no separate
/// theorem left to discharge.
///
/// The residual handling is the whole content. `unify` reports what one side had
/// left over, at most one side is non-empty (`M03.lemma_unify_disjoint`), and
/// `M03.lemma_unify_common` says the two segments extended by each other's
/// leftover are the SAME segment -- which is precisely the common instantiation
/// of the two implicit rows, and therefore the row at which each operand must be
/// instantiated here.
let dcompose (env:sig_env) (sa sb s:srow) (b_rest c_rest:seg)
             (_:squash (unify sa.post sb.pre == Some (b_rest, c_rest) /\
                        s == ({ pre = sa.pre @ c_rest; post = sb.post @ b_rest })))
             (f:cdenote env sa) (g:cdenote env sb)
  : cdenote env s =
  fun r stk ->
    lemma_unify_common sa.post sb.pre;
    append_assoc sa.pre  c_rest r;
    append_assoc sa.post c_rest r;
    append_assoc sb.pre  b_rest r;
    append_assoc sb.post b_rest r;
    fbind (f (c_rest @ r) stk) (g (b_rest @ r))

/// The easy case, for reference: when the producer's outputs exactly match the
/// consumer's inputs both residuals are empty, `unify` is `lemma_unify_refl`,
/// and `dcompose` degenerates to `fun r stk -> fbind (f r stk) (g r)` with no
/// transport at all. Everything above is the price of the general case.

(* ------------------------------------------------------------------------ *)
(* The primitive table's denotation                                         *)
(* ------------------------------------------------------------------------ *)

/// One denotation per row of `M05.prim_op`, mirroring `M06.prim_sig` exactly.
///
/// The signature is TAKEN, not computed. Writing the result type as
/// `xform (Some?.v (prim_sig p)).pre ...` would make every clause's expected type
/// an unreduced `option` projection under a capability test; taking `s` with a
/// `squash` of the table lookup lets the solver turn each row into two equations
/// about `s.pre` and `s.post` instead. `denote_static` takes its signature the
/// same way and for the same reason.
///
/// Every clause is a call into `M02` -- deliberately, and this is where D-55's
/// purity invariant is cashed out. `prim_den` returns an `xform`, a plain stack
/// function, with no `free` and no `env` anywhere in its type. A primitive
/// therefore *cannot* perform an operation: not by convention, but because it is
/// handed nothing that could. That is what makes T4 one case rather than twelve,
/// and it is the same argument `R02.apply_primop` makes on the machine side.
///
/// The capability premises are used, not bypassed: `SDup` goes through
/// `M02.vdup`, `SPick` through `M02.vpick`, `PRcRead` through `M02.vrc_read`,
/// each of which carries the `copyable` refinement that `prim_sig` established.
/// T6 is a statement about `M02`, so a hand-written duplication here would
/// silently put it out of reach.
///
/// `PUnroll` IS EXCLUDED BY THE REFINEMENT, not admitted. See the clause at the
/// foot of the table for why it has no denotation; excluding it is what keeps
/// T3, T4 and T6 unconditional statements about a well-defined fragment rather
/// than statements quantified over a case whose semantics does not exist.
let prim_den (p:prim_op { not (PUnroll? p) }) (s:srow)
             (_:squash (prim_sig p == Some s))
  : Tot (xform s.pre s.post) =
  match p with
  | PLit (LPrim pr v) -> (fun _ -> VCons (VPrim #pr v) VNil)

  | PStack (SDup d)       -> (fun stk -> vdup #d #[] stk)
  | PStack (SPop d)       -> (fun stk -> vpop #d #[] stk)
  | PStack (SSwap d1 d2)  -> (fun stk -> vswap #d1 #d2 #[] stk)
  | PStack (SPick above d) -> (fun stk -> vpick above #d #[] stk)
  | PStack (SRoll above d) ->
    (fun stk -> append_l_nil above; vroll_up above #d #[] stk)

  | PPack n caps repr   -> (fun stk -> append_l_nil repr; vseal n caps #repr #[] stk)
  | PUnpack n caps repr -> (fun stk -> append_l_nil repr;
                                   vunseal #n #caps #repr #[] stk)

  | PInj variants tag -> (fun stk -> VCons (VSum #variants tag stk) VNil)

  /// The tag order is fixed in `M02.vbool_sum` and `M01.bool_variants`: `false`
  /// is variant 0, `true` is variant 1.
  | PBoolSum -> (fun stk -> vbool_sum #[] stk)

  | PBoxNew d   -> (fun stk -> vbox_new  #d #[] stk)
  | PBoxOpen d  -> (fun stk -> vbox_open #d #[] stk)
  | PRcNew d    -> (fun stk -> vrc_new   #d #[] stk)
  | PRcClone d  -> (fun stk -> vrc_clone #d #[] stk)
  | PRcDrop d   -> (fun stk -> vrc_drop  #d #[] stk)
  | PRcRead d   -> (fun stk -> vrc_read  #d #[] stk)

  | PRoll n d   -> (fun stk -> vroll n #d #[] stk)

  /// EXCLUDED BY PRECONDITION, NOT ADMITTED: as `M06.prim_sig` types it, this
  /// clause HAS no denotation, and discovering that is the most useful thing
  /// writing this table did.
  ///
  /// `M02.VName #n #t v` hides the payload's type `t` as an implicit index, so
  /// nothing can recover it from a value of type `TName n`. `prim_sig` asks only
  /// for `wf d`, so `PRoll n d1` followed by `PUnroll n d2` typechecks for any
  /// well-formed `d2` and reinterprets a `d1` as a `d2`. That is a type-soundness
  /// violation, not a gap in this file, and `R02.apply_primop` makes both of
  /// these no-ops so the reference machine would happily run it.
  ///
  /// Discharging it needs BOTH halves, and only the first is cheap:
  ///
  ///   * TYPING: `wenv` gains a declaration table `w_types : list (nom_id & dtype)`
  ///     and `prim_sig` -- which would then have to take an environment -- requires
  ///     `d == lookup w_types n` for both rules. This is the LIMITATION already
  ///     recorded at `prim_sig`'s `PRoll` clause.
  ///   * VALUES: that alone is not enough. The typing fix says the two `d`s agree
  ///     with the declaration; it does not let anyone project `t` out of a
  ///     `VName`. Either `VName` stores its body type as an explicit field and
  ///     `vunroll` becomes decidably partial, or `value` gains a well-formedness
  ///     predicate relating `VName`s to `w_types` -- which is exactly the sort of
  ///     invariant-restoring obligation M02's header claims to have abolished.
  ///
  /// N02 Q-13 records the choice, because it is a design decision and not a
  /// proof step. Until it is made, `M05.uses_unroll` keeps such terms out of
  /// `denote_static`'s domain, so this clause is unreachable in the same sense
  /// `TSpecialize`'s is -- a genuine impossibility, and `make admits` correctly
  /// does not list it.
  | PUnroll _ _ -> false_elim ()

(* ------------------------------------------------------------------------ *)
(* A note where `coherent` used to be                                       *)
(* ------------------------------------------------------------------------ *)

/// A WORD CALL AND AN OPERATION CALL ARE THE SAME THING (D-60), and this module
/// is where that stopped being a slogan.
///
/// A word has a signature but no body anywhere in `wenv`, because a word's
/// meaning is whatever the ambient Dictionary says it is (D-37). So `TWord w`
/// denotes performing operation `w` -- and `M04.Op` insists the arguments have
/// shape `(op_of w).op_pre` while the signature says `(w_sig w).pre`. The two
/// must be the same segment.
///
/// This file used to state that as a predicate `coherent env` and refine
/// `denote_static` by it. THAT WAS THE WRONG FIX, and the reason is worth
/// keeping: `M06.wenv` carried two signature tables, P03 populated one of them
/// for a plain `define`, and so the refinement was unsatisfied for every program
/// the REPL could actually elaborate. A denotation nothing real satisfies is not
/// a semantics with a caveat, it is a semantics for nothing -- the spec and the
/// implementation drifting apart at precisely the point where the spec is
/// supposed to mean something.
///
/// D-63 removed the second table instead. `M06.w_sig` now reads from `w_ops`, so
/// the agreement is definitional, `coherent` is `True` and has been deleted, and
/// P03 cannot regress: a word absent from `w_ops` has no signature at all rather
/// than a stale one that disagrees.
///
/// The observation the predicate was trying to express survives, and it is D-01
/// turning up where it can be checked: the Dictionary is a handler (M10), a word
/// call is an operation of it, and resolving a word statically is `M04.handle`
/// run at elaboration time -- which is `M11.specialize`.

(* ------------------------------------------------------------------------ *)
(* Branches                                                                 *)
(* ------------------------------------------------------------------------ *)

/// One arm of a `case`: the branch run after its variant's payload is in place.
///
/// NOT a `cdenote`, and the reason is worth stating. `M06.infer_branches` types
/// an arm as `compose ( -- v_i ) s_i`, treating the payload as if some program
/// had pushed it. No program did: the payload comes out of the scrutinee. So the
/// payload is a separate argument here, and `arm.pre` is only what the branch
/// needs BEYOND it.
let dcase_arm (env:sig_env) (v:seg) (sb:srow) (arm:srow) (b_rest c_rest:seg)
              (_:squash (unify v sb.pre == Some (b_rest, c_rest) /\
                         arm == ({ pre = c_rest; post = sb.post @ b_rest })))
              (f:cdenote env sb)
              (r:seg) (payload:vstack v) (rest:vstack (arm.pre @ r))
  : Tot (free env (arm.post @ r)) =
  lemma_unify_common v sb.pre;
  append_assoc v c_rest r;
  append_assoc sb.pre  b_rest r;
  append_assoc sb.post b_rest r;
  f (b_rest @ r) (vappend payload rest)

(* ------------------------------------------------------------------------ *)
(* Handler implementations                                                  *)
(* ------------------------------------------------------------------------ *)

/// Find an implementation, carrying the two facts the recursion needs about it:
/// its body is small enough for the termination measure, and it inherits the
/// staging restriction from the handler as a whole. Both are packaged into the
/// refinement because the alternative is two separate inductions at the call
/// site, inside a lambda over `op_id` where they are awkward to state.
let rec impl_lookup (impls:list (op_id & term)) (op:op_id)
  : Tot (option (b:term { term_size b <= impls_size impls /\
                          (not (needs_compiler_impls impls) ==>
                           not (needs_compiler b)) /\
                          (not (uses_unroll_impls impls) ==>
                           not (uses_unroll b)) }))
        (decreases impls) =
  match impls with
  | []             -> None
  | (o, b) :: rest ->
    if o = op then Some b
    else (match impl_lookup rest op with
          | None    -> None
          | Some b' -> Some b')

/// Inversion of `M06.infer_impls`: whatever `impl_lookup` finds was checked at
/// the operation's declared signature with the handler state framed on top. This
/// is the only thing `denote_static`'s `THandle` clause needs to know about
/// `infer_impls`, and it has to be a separate induction because `h_ops` is a
/// function of `op` and so cannot recurse on the list.
let rec lemma_impl_typed (env:wenv) (eff:eff_id) (st:seg)
                         (impls:list (op_id & term)) (op:op_id)
  : Lemma (requires Some? (infer_impls env eff st impls) /\
                    Some? (impl_lookup impls op))
          (ensures  (let Some b = impl_lookup impls op in
                     let osig = op_of env.w_ops op in
                     Some? (infer env b) /\
                     fst (Some?.v (infer env b))
                       == ({ pre  = st @ osig.op_pre
                           ; post = st @ osig.op_post })))
          (decreases impls) =
  match impls with
  | []             -> ()
  | (o, b) :: rest -> if o = op then () else lemma_impl_typed env eff st rest op

(* ------------------------------------------------------------------------ *)
(* The denotation function                                                  *)
(* ------------------------------------------------------------------------ *)

/// The meaning of a well-typed program that needs no compiler stage.
///
/// WHAT "STATIC" MEANS HERE (D-61): `not (needs_compiler t)`, i.e. no
/// `TSpecialize` anywhere in the term. That is the exact fragment whose meaning
/// is fixed without running the specializer, and `M11.stage_required` already
/// uses the same predicate to decide whether a binary needs a compiler linked
/// into it at all. `TSpecialize`'s denotation is M11's E2, which is stated
/// against this function, so defining it here would be circular.
///
/// THE SECOND CONJUNCT IS A DEFECT MARKER, NOT A DESIGN BOUNDARY (D-62).
/// `not (uses_unroll t)` excludes `PUnroll`, which as `M06.prim_sig` types it has
/// no denotation at all -- see `prim_den`. It is in the precondition rather than
/// admitted in the table because the difference is not cosmetic: a function that
/// is total by fiat on a case whose semantics does not exist makes T3, T4 and T6
/// conditional on a fix nobody has made, since each is quantified over terms
/// containing that case. Excluded, the same theorems are unconditional statements
/// about a well-defined fragment, and the fragment grows when roll/unroll is
/// settled. It also means this module has no `admit`.
///
/// The signature and effect row are TAKEN as arguments with a `squash` of the
/// `infer` equation, rather than computed as `fst (Some?.v (infer env t))`. This
/// is the change that makes the definition possible at all: with the index
/// computed, every recursive call's type mentions an unreduced `infer env a`, and
/// the `TSeq` clause has no way to say that the composite's shape is built from
/// the operands' shapes. Taking them lets each clause turn the `infer` equation
/// into ordinary equations between segments, which is what the transport needs.
let rec denote_static (env:wenv) (t:term) (s:srow) (e:erow)
                      (_:squash (not (needs_compiler t) /\ not (uses_unroll t) /\
                                 infer env t == Some (s, e)))
  : Tot (cdenote env.w_ops s) (decreases %[(term_size t <: nat); 0]) =
  match t with
  /// Identity of the category.
  | TNil -> dnil env.w_ops

  /// Composition in the category -- T2, by construction.
  | TSeq a b ->
    let Some (sa, ea) = infer env a in
    let Some (sb, eb) = infer env b in
    let Some (b_rest, c_rest) = unify sa.post sb.pre in
    dcompose env.w_ops sa sb s b_rest c_rest ()
             (denote_static env a sa ea ())
             (denote_static env b sb eb ())

  /// Every intrinsic, in one clause, because every intrinsic is pure (D-55).
  | TPrimOp p -> dpure env.w_ops s (prim_den p s ())

  /// A WORD IS AN OPERATION OF THE DICTIONARY (D-37, D-60). There is no body to
  /// inline: `wenv` records a word's signature, never its definition, because
  /// which definition it has is exactly what the ambient Dictionary decides. So
  /// the denotation performs `w` and resumes with the results in place, and it is
  /// `M04.handle` -- at elaboration time in `M11.specialize`, at runtime in
  /// `R02.find_handler` -- that supplies the meaning.
  ///
  /// The argument segment `(w_sig env w).pre` is passed where `M04.Op` demands
  /// `(op_of env.w_ops w).op_pre`, and that typechecks with no side condition
  /// because `M06.w_sig` IS `sig_of_op (op_of ...)` (D-63). Before that, the two
  /// were separate tables and this line needed a `coherent env` refinement that
  /// P03 did not satisfy.
  | TWord w ->
    (fun r stk ->
      let (arg, rest) = vsplit (w_sig env w).pre #r stk in
      Op w arg (on _ (fun res -> Pure (vappend res rest))))

  /// Sum elimination. The scrutinee's tag selects the branch, and `denote_case`
  /// walks the variant and branch lists together -- mirroring `infer_branches`,
  /// which is what makes the join's framing available structurally instead of by
  /// a separate inversion lemma.
  | TCase variants branches ->
    let Some (j, row) = infer_branches env variants branches in
    (fun r stk ->
      let VCons (VSum tag payload) rest = stk in
      denote_case env variants branches j row () r tag payload rest)

  /// Handling. `M04.handle` does the work; everything here is assembling its
  /// arguments.
  ///
  /// The state comes from `init`, which may itself perform effects, so it is
  /// obtained monadically rather than as a value -- `fbind` before `handle`. An
  /// unimplemented operation gets `M04.fwd_impl`, which forwards it outward, and
  /// that is the semantic content of `infer_impls` not requiring every operation
  /// of the effect to appear.
  | THandle eff st init impls body ->
    let Some (si, ei)        = infer env init in
    let Some (sbody, rbody)  = infer env body in
    let hdl : handler env.w_ops eff st = {
      h_ops = (fun op ->
        match impl_lookup impls op with
        | None   -> fwd_impl env.w_ops st op
        | Some b ->
          lemma_impl_typed env eff st impls op;
          let Some (sb, eb) = infer env b in
          append_l_nil sb.pre;
          append_l_nil sb.post;
          (fun args -> denote_static env b sb eb () [] args))
    } in
    (fun r stk ->
      append_l_nil st;
      append_assoc st sbody.post r;
      fbind (denote_static env init si ei () [] VNil)
            (fun state -> handle hdl state
                              (denote_static env body sbody rbody () r stk)))

  /// Unreachable: `needs_compiler (TSpecialize _)` is `true`, which the
  /// precondition denies. Stated as `false_elim` rather than `admit` because it
  /// is a genuine impossibility and not a gap -- `make admits` should not list it.
  | TSpecialize _ -> false_elim ()

/// The branch dispatch of a `case`, walking variants and branches in step.
///
/// `j` is the joined signature `infer_branches` computed and `r` the ambient row.
/// At each step `M03.srow_join` has framed this branch's arm by `r2` and the rest
/// of the join by `r1`, and `M03.lemma_unify_common` is what says those two
/// framings land on the same segment -- so taking branch 0 means instantiating
/// its arm at `r2 @ r`, and skipping it means recursing at `r1 @ r`. That is the
/// whole reason a `case` may have branches of different depths.
and denote_case (env:wenv)
                (variants:list seg) (branches:list term)
                (j:srow) (row:erow)
                (_:squash (not (needs_compiler_list branches) /\
                           not (uses_unroll_list branches) /\
                           length branches == length variants /\
                           infer_branches env variants branches == Some (j, row)))
                (r:seg) (tag:nat { tag < length variants })
                (payload:vstack (index variants tag))
                (rest:vstack (j.pre @ r))
  : Tot (free env.w_ops (j.post @ r)) (decreases %[terms_size branches; 1]) =
  match variants, branches with
  /// Both impossible: no tag is below zero, and the lengths agree.
  | [], _ -> false_elim ()
  | _, [] -> false_elim ()

  | [v], [b] ->
    let Some (sb, eb) = infer env b in
    let Some (b_rest, c_rest) = unify v sb.pre in
    dcase_arm env.w_ops v sb j b_rest c_rest ()
              (denote_static env b sb eb ()) r payload rest

  | v :: vs, b :: bs ->
    let Some (sb, eb) = infer env b in
    let Some (b_rest, c_rest) = unify v sb.pre in
    let arm : srow = { pre = c_rest; post = sb.post @ b_rest } in
    let Some (jrest, e') = infer_branches env vs bs in
    let Some (r1, r2) = unify arm.pre jrest.pre in
    if tag = 0
    then begin
      append_assoc arm.pre  r2 r;
      append_assoc arm.post r2 r;
      dcase_arm env.w_ops v sb arm b_rest c_rest ()
                (denote_static env b sb eb ()) (r2 @ r) payload rest
    end
    else begin
      lemma_unify_common arm.pre jrest.pre;
      append_assoc arm.pre    r2 r;
      append_assoc jrest.pre  r1 r;
      append_assoc jrest.post r1 r;
      denote_case env vs bs jrest e' () (r1 @ r) (tag - 1) payload rest
    end

(* ------------------------------------------------------------------------ *)
(* T1: the empty program is the identity                                    *)
(* ------------------------------------------------------------------------ *)

/// Proved, not admitted. `infer env TNil` reduces to `Some (sid, pure_row)` and
/// the `TNil` clause is `dnil`, so this is now definitional.
let thm_denote_nil (env:wenv) (r:seg) (stk:vstack r)
  : Lemma (denote_static env TNil sid pure_row () r stk == Pure stk) = ()

(* ------------------------------------------------------------------------ *)
(* Non-vacuity: a denotation that computes                                  *)
(* ------------------------------------------------------------------------ *)

/// `make interp` exists because a specification that typechecks may still denote
/// nothing usable; this section is the same check for the denotational side. A
/// `cdenote` is a function, so a definition riddled with transport could be
/// well typed and still not reduce to an answer. These lemmas are discharged by
/// conversion, which is the evidence that it does.
///
/// The empty environment. Every word in it is undeclared, hence `( -- )` at
/// `!Dict` — which is why the examples below use no words at all.
let empty_wenv : wenv = { w_effs = []; w_ops = empty_sig_env }

/// `2 3`: two literals in sequence. Small, but it exercises the case that
/// mattered -- `TSeq` with a non-empty residual. The producer leaves an `i64` the
/// consumer does not take, so `unify` returns `([i64], [])` and `dcompose` has to
/// instantiate the second literal's implicit row at `[i64]` rather than at `[]`.
/// A `TSeq` clause that ignored the residual would fail here and nowhere simpler.
let ex_two : term =
  TSeq (TPrimOp (PLit (LPrim PI64 2))) (TPrimOp (PLit (LPrim PI64 3)))

let ex_two_sig : srow = { pre = []; post = [TPrim PI64; TPrim PI64] }

let lemma_ex_two_typed ()
  : Lemma (infer empty_wenv ex_two == Some (ex_two_sig, pure_row)) = ()

/// Head of the index list is the top of the stack, so `3` is on top.
let lemma_ex_two_denote ()
  : Lemma (denote_static empty_wenv ex_two ex_two_sig pure_row () [] VNil
           == Pure (VCons (VPrim #PI64 3) (VCons (VPrim #PI64 2) VNil))) = ()

/// The branching case, which is where the bookkeeping actually is. This is
/// `7 true if { } then { pop 9 } endif` in the core:
///
///   * `PBoolSum` coerces the `bool` to `M01.bool_variants` (D-33);
///   * branch 0 is `( -- )` and branch 1 is `( i64 -- i64 )`, so the two do NOT
///     have equal signatures and are joined only because framing branch 0 by
///     `[i64]` makes them agree (`M03.srow_join`, D-34's else-less rule);
///   * the tag is 1, so `denote_case` takes its skipping path and has to carry
///     the join residual `r1` into the recursive row.
///
/// Every one of those is a place a definition could be well typed and wrong.
/// That the answer comes out by conversion is the check.
let ex_dec : term =
  TSeq (TPrimOp (PStack (SPop (TPrim PI64)))) (TPrimOp (PLit (LPrim PI64 9)))

let ex_if : term =
  seq_of [ TPrimOp (PLit (LPrim PI64 7))
         ; TPrimOp (PLit (LPrim PBool true))
         ; TPrimOp PBoolSum
         ; TCase bool_variants [TNil; ex_dec] ]

let ex_if_sig : srow = { pre = []; post = [TPrim PI64] }

/// `assert_norm` rather than `()`, and the difference is fuel, not difficulty.
/// The two-literal example above is discharged by the solver's own unfolding of
/// `infer`; this one is six `TSeq` levels deep with an `infer_branches` fold
/// inside, which is past the default. `assert_norm` runs the normalizer instead,
/// so what is being checked is still conversion.
let lemma_ex_if_typed ()
  : Lemma (infer empty_wenv ex_if == Some (ex_if_sig, pure_row)) =
  assert_norm (infer empty_wenv ex_if == Some (ex_if_sig, pure_row))

/// Named rather than passed as `()`, because `denote_static`'s precondition
/// appears in the STATEMENT below and so has to be discharged while that
/// statement is being typechecked, where a lemma call in the body is too late.
let ex_if_pf : squash (not (needs_compiler ex_if) /\ not (uses_unroll ex_if) /\
                       infer empty_wenv ex_if == Some (ex_if_sig, pure_row)) =
  assert_norm (not (needs_compiler ex_if) /\ not (uses_unroll ex_if) /\
               infer empty_wenv ex_if == Some (ex_if_sig, pure_row))

let lemma_ex_if_denote ()
  : Lemma (denote_static empty_wenv ex_if ex_if_sig pure_row ex_if_pf [] VNil
           == Pure (VCons (VPrim #PI64 9) VNil)) =
  assert_norm (denote_static empty_wenv ex_if ex_if_sig pure_row ex_if_pf [] VNil
               == Pure (VCons (VPrim #PI64 9) VNil))

(* ------------------------------------------------------------------------ *)
(* The obligations, as types                                                *)
(* ------------------------------------------------------------------------ *)

/// AN OBLIGATION IS A TYPE; DISCHARGING IT IS EXHIBITING A VALUE (D-64).
///
/// The prose block at the foot of this file used to be the only statement of
/// T1-T6, and prose has a specific failure mode this development already hit:
/// T5 WAS FALSE FOR THREE COMMITS and nothing could tell, because a comment
/// mentions `within` and `row` without either being the real one. A type
/// mentions the real ones or it does not typecheck.
///
/// What is deliberately NOT done here is `assume val`. That would make each
/// obligation available to later proofs, and T5's history is the argument
/// against it: assuming a false lemma is not an incomplete development, it is an
/// inconsistent one. A bare type is the safe half of the idea -- checked as a
/// statement, worthless as a hypothesis, which is exactly right for something
/// unproved.
///
/// So the pattern is: the type below is the obligation, a value of it is the
/// theorem, and `denote_laws` at the end collects them. `t1_type` and `t2_type`
/// are inhabited. The rest are not, and the absence of a value IS the gap --
/// visible to the typechecker rather than to a reader who happens to scroll.

/// T1. The empty program is the identity, at every row.
let t1_type : Type =
    (env:wenv) -> (r:seg) -> (stk:vstack r)
  -> Lemma (denote_static env TNil sid pure_row () r stk == Pure stk)

/// T2. Juxtaposition denotes composition along `M03.compose`.
///
/// Stating it against `denote_static` rather than pointing at `dcompose` is what
/// keeps "true by construction" honest: the equation is what a reader wants
/// checked, and if the `TSeq` clause is ever rewritten this is what notices.
let t2_type : Type =
    (env:wenv) -> (a:term) -> (b:term)
  -> (sa:srow) -> (sb:srow) -> (s:srow)
  -> (ea:erow) -> (eb:erow) -> (e:erow)
  -> (b_rest:seg) -> (c_rest:seg)
  -> (pfa:squash (not (needs_compiler a) /\ not (uses_unroll a) /\
                  infer env a == Some (sa, ea)))
  -> (pfb:squash (not (needs_compiler b) /\ not (uses_unroll b) /\
                  infer env b == Some (sb, eb)))
  -> (pf:squash (not (needs_compiler (TSeq a b)) /\ not (uses_unroll (TSeq a b)) /\
                 infer env (TSeq a b) == Some (s, e) /\
                 unify sa.post sb.pre == Some (b_rest, c_rest) /\
                 s == ({ pre = sa.pre @ c_rest; post = sb.post @ b_rest })))
  -> Lemma (denote_static env (TSeq a b) s e pf
            == dcompose env.w_ops sa sb s b_rest c_rest ()
                        (denote_static env a sa ea pfa)
                        (denote_static env b sb eb pfb))

/// T3. Naturality in the row: a program does not disturb the stack beneath it.
///
/// The two `append_assoc` equations are hypotheses rather than lemma calls
/// because a `Lemma` statement cannot run a tactic before typechecking itself,
/// and without them `vappend x y` and the argument of `denote_static ... (r @ r')`
/// have propositionally-but-not-definitionally equal types. They are always
/// true; carrying them costs a line and keeps the statement well formed.
let t3_type : Type =
    (env:wenv) -> (t:term) -> (s:srow) -> (e:erow)
  -> (pf:squash (not (needs_compiler t) /\ not (uses_unroll t) /\
                 infer env t == Some (s, e)))
  -> (r:seg) -> (r':seg)
  -> (_:squash ((s.pre @ r) @ r' == s.pre @ (r @ r') /\
                (s.post @ r) @ r' == s.post @ (r @ r')))
  -> (x:vstack (s.pre @ r)) -> (y:vstack r')
  -> Lemma (denote_static env t s e pf (r @ r') (vappend x y)
            == fbind (denote_static env t s e pf r x)
                     (fun z -> Pure (vappend z y)))

/// T4. Purity is real: a program with an empty row performs no operation.
let t4_type : Type =
    (env:wenv) -> (t:term) -> (s:srow) -> (e:erow)
  -> (pf:squash (not (needs_compiler t) /\ not (uses_unroll t) /\
                 infer env t == Some (s, e)))
  -> (r:seg) -> (stk:vstack (s.pre @ r))
  -> Lemma (requires is_pure env t)
           (ensures  Pure? (denote_static env t s e pf r stk))

/// T5. Effect-row soundness: every operation the denotation can perform is in
/// the row the type system computed.
let t5_type : Type =
    (env:wenv) -> (t:term) -> (s:srow) -> (e:erow)
  -> (pf:squash (not (needs_compiler t) /\ not (uses_unroll t) /\
                 infer env t == Some (s, e)))
  -> (r:seg) -> (stk:vstack (s.pre @ r))
  -> Lemma (within e (denote_static env t s e pf r stk))

/// T1, DISCHARGED. `infer env TNil` reduces to `Some (sid, pure_row)` and the
/// `TNil` clause is `dnil`, so this is definitional.
let thm_t1 : t1_type = fun env r stk -> ()

/// T2, DISCHARGED. Also definitional -- the `TSeq` clause IS this call. That the
/// proof is `()` is the content of "by construction", and now it is a proof
/// rather than a claim about one.
let thm_t2 : t2_type =
  fun env a b sa sb s ea eb e b_rest c_rest pfa pfb pf -> ()

/// The bundle. UNINHABITED TODAY, deliberately: `t3`, `t4` and `t5` have no
/// values, so this record cannot be built, and that is the honest gap in the
/// form the typechecker can see. Filling it is the work M09's S-series depends
/// on.
///
/// T6 IS ABSENT BECAUSE IT CANNOT YET BE STATED, which is a different kind of
/// gap and should not be disguised as this one. "No denotation duplicates a
/// value of a non-copyable type" needs an erasure from `vstack` to a multiset of
/// leaf values, and M02 has no such function; until it does, T6 has no type to
/// be the type of. See the prose below.
noeq type denote_laws = {
  dl_t1 : t1_type;
  dl_t2 : t2_type;
  dl_t3 : t3_type;
  dl_t4 : t4_type;
  dl_t5 : t5_type;
}

(* ------------------------------------------------------------------------ *)
(* Remaining obligations                                                    *)
(* ------------------------------------------------------------------------ *)

/// THE STATEMENTS NOW LIVE ABOVE, AS `t1_type` .. `t5_type` (D-64). What follows
/// is the RATIONALE -- why each matters, what it costs, and which case is the
/// hard one -- which is the part a type cannot carry. Where the two disagree the
/// type wins, because it is the one the checker reads.
///
/// All of them are quantified over `denote_static`'s domain, which is the
/// well-typed fragment minus `TSpecialize` and minus `PUnroll`. That is a real
/// restriction and it is stated once here rather than repeated: because both
/// exclusions are preconditions rather than admitted clauses, each obligation
/// below is an UNCONDITIONAL claim about that fragment, and none of them is
/// silently contingent on the roll/unroll hole being fixed first (D-62).

/// T1  THE EMPTY PROGRAM IS THE IDENTITY.  *** DISCHARGED, as `thm_t1`. ***
///
/// T2  SEQUENCING IS KLEISLI COMPOSITION.  *** DISCHARGED, as `thm_t2`. ***
///     `dcompose` above is the statement, and the `TSeq` clause is a call to it.
///     What licenses treating any word as a black box given only its signature
///     and row -- and therefore the optimiser's DAG view and incremental
///     re-checking -- is now the definition rather than a pending theorem.
///
///     PRECISELY WHAT WAS DISCHARGED, because "by construction" overclaims if
///     left unqualified. `dcompose` takes a `squash` that `M03.unify` returned
///     the residuals `(b_rest, c_rest)` and that the composite is
///     `{ pre = sa.pre @ c_rest; post = sb.post @ b_rest }`; it does not prove
///     that this is the right signature, it assumes it and then transports the
///     stack across it. The transport is where the work is, and it is discharged
///     by `M03.lemma_unify_common` and `append_assoc`. So the residue of T2 is
///     the correctness of `M03.compose`, which lives in M03 and is proved there
///     -- `lemma_unify_disjoint`, `lemma_unify_common`, `lemma_compose_assoc`.
///     The theorem relocated; it did not evaporate. What the relocation buys is
///     that composition is written ONCE, so no clause of `denote_static` can get
///     it wrong independently.
///
///     `M03.srow_is_partial_monoid` is where the relocated half now lives as a
///     value rather than as three separate lemmas, so "T2 rests on M03" is
///     checkable too. And `thm_t2` proves the equation about `denote_static`
///     itself by `()`, which is what "by construction" was asserting.
///
/// T3  NATURALITY IN THE ROW.
///     For all `r`, `r'`, `x : vstack s.pre`, `y : vstack r`:
///         denote_static t (r @ r') (vappend x y)  pushes `y` through unchanged.
///     `dframe` is the combinator form and is proved. It is the general form of
///     "a word does not disturb the stack beneath it".
///
///     MOST CASES ARE ROUTINE AND `THandle` IS NOT, which is worth recording
///     before anyone budgets the induction as uniform. The structural cases are
///     an appeal to `M02.lemma_frame_apply` plus one `append_assoc`. `THandle`
///     is different in kind: the obligation is that `M04.handle` COMMUTES WITH
///     FRAMING, and `handle` is a fold that prepends its state segment `st` to
///     the result -- so the statement to prove relates `handle h state (m at row
///     r @ r')` to `handle h state (m at row r)` framed by `r'`, with `st`
///     sitting between the two appends on one side and not the other. That is a
///     `st @ (a @ r')` versus `(st @ a) @ r'` mismatch under a recursive fold
///     whose `Op` case is guarded by a runtime test, which is the same shape
///     that makes M10's H2 and H3 hard. Expect T3's `THandle` case to cost what
///     H2 costs, and probably to share a lemma with it.
///
/// T4  PURITY IS REAL.
///     If `is_pure env t` then `denote_static env t s e () r stk` is `Pure _`.
///     THE PRIMITIVE CASE IS FREE, and that is what D-55 bought: `prim_den`
///     returns an `xform`, which has no `free` in its type, so no `Op` node can
///     be built there whatever the row. The remaining cases are `TWord` --
///     which is where the statement has real content, and which needs T5's
///     correction below, since a pure row must then exclude `!Dict` -- and the
///     structural ones.
///
/// T5  EFFECT-ROW SOUNDNESS.  *** REPAIRED; TRUE AS ORIGINALLY STATED. ***
///     If `infer env t = Some (_, row)` then `within row (denote_static env t s e
///     () r stk)`. Every operation the denotation can perform is listed in the
///     row the type system computed.
///
///     IT WAS FALSE, AND WHY IS WORTH KEEPING. The `TWord` clause refuted it: a
///     word `w` with an empty row denotes `Op w ...`, and `within` requires
///     `eff_of w` to appear in the row, so an ordinary pure-looking word violated
///     its own row. Not a defect in the denotation -- D-37 collecting its debt.
///     That decision left `!Dict` implicit on the stated grounds that
///     `M04.within` never sees it. `within` saw it as soon as a denotation
///     existed.
///
///     D-63 repaired it at the source rather than weakening the statement.
///     `M04.eff_dict` is a reserved id, `M06.w_eff` DERIVES the entry
///     `(eff_of w, stage_of w)` at the head of every word's row instead of
///     trusting a stored one, so the `TWord` case now holds by unfolding. There
///     is no `dict_row` prefix in the statement and no special case anywhere.
///
///     STILL AN OBLIGATION, and the remaining content is the induction: `TSeq`
///     needs `M04.lemma_within_weaken` on each side of `row_union`, `TCase`
///     needs it across the branch fold, and `THandle` is the interesting case
///     because `row_remove eff` genuinely narrows the row -- which is M10's H1,
///     including its proviso that an implementation performing its own effect
///     does not discharge it.
///
/// T6  CAPABILITY SOUNDNESS.
///     No denotation duplicates a value of a non-copyable type or discards a
///     value of a non-droppable type. Formally: erasing to a multiset of leaf
///     values, a linear slot occurs exactly once in the output whenever it
///     occurred once in the input.
///
///     The statement is about `M02`, not about this file, and that is now true by
///     construction rather than by inspection: every clause of `prim_den` calls
///     an `M02` operation, so the only places a value is duplicated or dropped
///     are `vdup`, `vpick`, `vpop`, `vrc_clone`, `vrc_read` and `vrc_drop`, each
///     carrying its capability refinement. `M02.vpick` and `M02.vroll_up` were
///     added for exactly this reason -- hand-writing the deep accesses here would
///     have put a duplication outside the file T6 quantifies over.
