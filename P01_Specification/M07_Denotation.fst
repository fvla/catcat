module M07_Denotation

/// catcat core specification, module 07: denotational semantics.
///
/// A well-typed program denotes a row-polymorphic, effectful stack
/// transformer. Sequencing denotes Kleisli composition in the free monad, so
/// the draft's claim that "a program is a complete composition of functions,
/// without reference to data" stops being a slogan and becomes the *definition*
/// of the `TSeq` clause below -- T2 is now true by construction rather than by
/// proof.
///
/// STATUS: `denote_static` is DEFINED, for the whole core except `TSpecialize`
/// (D-61). One clause is admitted, `PUnroll`, and it is admitted because it is
/// not definable: writing the denotation is what exposed a genuine soundness
/// hole in M06's roll/unroll rules (see `prim_den` and N02 Q-11).
///
/// THREE THINGS FELL OUT OF WRITING THIS, none of which was visible from the
/// typing rules alone. They are the reason a denotation is worth having even
/// before any theorem is proved about it:
///
///   1. `TWord w` denotes `Op w` -- a word call and an operation call are the
///      SAME node of the free monad. That is D-37 and D-01 made semantic, and it
///      forces `coherent` below.
///   2. `wenv`'s two tables must agree. Nothing in M06 required it, and the
///      denotation cannot be written without it (D-60).
///   3. T5 is FALSE as it was stated, because a plain word's denotation performs
///      an operation its row does not mention. `!Dict` has to be a real row
///      entry, not an elided convention. See the restatement at the foot of this
///      file.

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
let prim_den (p:prim_op) (s:srow) (_:squash (prim_sig p == Some s))
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

  /// ADMITTED, AND NOT MERELY UNPROVED: as `M06.prim_sig` types it, this clause
  /// HAS no denotation, and discovering that is the most useful thing writing
  /// this table did.
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
  /// N02 Q-11 records the choice, because it is a design decision and not a
  /// proof step.
  | PUnroll _ _ -> admit ()

(* ------------------------------------------------------------------------ *)
(* Coherence of the word environment                                        *)
(* ------------------------------------------------------------------------ *)

/// A WORD CALL AND AN OPERATION CALL ARE THE SAME THING (D-60), and this is the
/// condition that makes that sayable.
///
/// `M06.wenv` carries two tables: `w_defs`, giving each word a signature and an
/// effect row, and `w_ops`, giving each operation an effect and a signature.
/// Nothing in M06 relates them, and nothing had to -- until the denotation of
/// `TWord w` had to be written. A word has a signature but no body anywhere in
/// `wenv`, because a word's meaning is whatever the ambient Dictionary says it
/// is (D-37). So `TWord w` denotes performing operation `w`, and `M04.Op` insists
/// the arguments have shape `(op_of w).op_pre` while the signature says
/// `(w_sig w).pre`. The two must be the same segment.
///
/// This is not a technicality imposed by the encoding; it is D-01 turning up
/// where it can be checked. The Dictionary is a handler (M10), a word call is an
/// operation of it, and resolving a word statically is `M04.handle` run at
/// elaboration time -- which is `M11.specialize`.
///
/// Note that it holds VACUOUSLY for words in neither table: `wd_unknown.wd_sig`
/// is `sid` and `op_unknown.od_sig` is `( -- )`, and `sig_of_op` of the latter is
/// `sid`. So the condition constrains exactly the words some table mentions,
/// which is what it should do.
///
/// P03 DOES NOT CURRENTLY SATISFY THIS. `E06_Repl` registers an `effect`'s
/// operations in both tables (coherent), but a plain `define` goes into `w_defs`
/// only, leaving `op_of` at `( -- )`. Fixing it means giving defined words an
/// entry in `w_ops` under a reserved `Dict` effect id -- which is the same change
/// T5 below needs, and is recorded as such rather than done here, because it
/// changes what the REPL prints.
let coherent (env:wenv) : Type0 =
  forall (w:word_id). w_sig env w == sig_of_op (op_of env.w_ops w)

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
                           not (needs_compiler b)) }))
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
/// The signature and effect row are TAKEN as arguments with a `squash` of the
/// `infer` equation, rather than computed as `fst (Some?.v (infer env t))`. This
/// is the change that makes the definition possible at all: with the index
/// computed, every recursive call's type mentions an unreduced `infer env a`, and
/// the `TSeq` clause has no way to say that the composite's shape is built from
/// the operands' shapes. Taking them lets each clause turn the `infer` equation
/// into ordinary equations between segments, which is what the transport needs.
let rec denote_static (env:wenv { coherent env }) (t:term) (s:srow) (e:erow)
                      (_:squash (not (needs_compiler t) /\
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
  /// `coherent env` is what lets the argument segment `(w_sig env w).pre` be
  /// passed where `M04.Op` demands `(op_of env.w_ops w).op_pre`.
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
and denote_case (env:wenv { coherent env })
                (variants:list seg) (branches:list term)
                (j:srow) (row:erow)
                (_:squash (not (needs_compiler_list branches) /\
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
let thm_denote_nil (env:wenv { coherent env }) (r:seg) (stk:vstack r)
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
/// The empty environment is coherent: `wd_unknown.wd_sig` is `sid`, `op_unknown`
/// is `( -- )`, and `sig_of_op` of the latter is `sid` too.
let empty_wenv : wenv = { w_defs = []; w_ops = empty_sig_env }

let lemma_empty_coherent () : Lemma (coherent empty_wenv) = ()

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
let ex_if_pf : squash (not (needs_compiler ex_if) /\
                       infer empty_wenv ex_if == Some (ex_if_sig, pure_row)) =
  assert_norm (not (needs_compiler ex_if) /\
               infer empty_wenv ex_if == Some (ex_if_sig, pure_row))

let lemma_ex_if_denote ()
  : Lemma (denote_static empty_wenv ex_if ex_if_sig pure_row ex_if_pf [] VNil
           == Pure (VCons (VPrim #PI64 9) VNil)) =
  assert_norm (denote_static empty_wenv ex_if ex_if_sig pure_row ex_if_pf [] VNil
               == Pure (VCons (VPrim #PI64 9) VNil))

(* ------------------------------------------------------------------------ *)
(* Remaining obligations                                                    *)
(* ------------------------------------------------------------------------ *)

/// T2  SEQUENCING IS KLEISLI COMPOSITION.  *** DISCHARGED, BY CONSTRUCTION. ***
///     `dcompose` above is the statement, and the `TSeq` clause is a call to it.
///     What licenses treating any word as a black box given only its signature
///     and row -- and therefore the optimiser's DAG view and incremental
///     re-checking -- is now the definition rather than a pending theorem.
///
/// T3  NATURALITY IN THE ROW.
///     For all `r`, `r'`, `x : vstack s.pre`, `y : vstack r`:
///         denote_static t (r @ r') (vappend x y)  pushes `y` through unchanged.
///     `dframe` is the combinator form and is proved; the statement about
///     `denote_static` itself is an induction over the term whose every case is
///     an appeal to `M02.lemma_frame_apply` plus one `append_assoc`. It is the
///     general form of "a word does not disturb the stack beneath it".
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
/// T5  EFFECT-ROW SOUNDNESS.  *** FALSE AS PREVIOUSLY STATED. ***
///     It read: if `infer env t = Some (_, row)` then `within row (denote env t r stk)`.
///     The `TWord` clause refutes it. A word `w` with an empty row denotes
///     `Op w ...`, and `within` requires `eff_of w` to appear in the row, so the
///     denotation of an ordinary pure-looking word violates its own row.
///
///     This is not a defect in the denotation. It is D-37 collecting its debt:
///     "a word's meaning always depends on the dictionary it was elaborated
///     against, and `!Dict` is the direct encoding of that fact." D-37 chose to
///     leave `!Dict` implicit on the grounds that `M04.within` never sees it.
///     `within` sees it now.
///
///     The corrected statement, and the change it requires:
///         within (dict_row @ row) (denote_static env t s e () r stk)
///     where `dict_row` is the singleton row of a RESERVED `Dict` effect id, and
///     `M06.w_eff` returns it for every word that is not a declared operation.
///     Equivalently: reserve the id, register defined words in `w_ops` under it
///     (which is also what `coherent` needs from P03), and T5 becomes true as
///     originally written with no special case at all. That is the better fix and
///     it is a change to M04/M06, not to this file.
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
