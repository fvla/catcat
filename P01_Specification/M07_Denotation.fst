module M07_Denotation

/// catcat core specification, module 07: denotational semantics.
///
/// A well-typed program denotes a row-polymorphic, effectful stack
/// transformer. Sequencing denotes Kleisli composition in the free monad, so
/// the draft's claim that "a program is a complete composition of functions,
/// without reference to data" stops being a slogan and becomes theorem T2
/// below.
///
/// STATUS: skeleton. `cdenote`, `dnil` and `dpure` are real and checked.
/// `denote` is declared but not defined. The remaining theorems are stated as
/// obligations rather than as `Lemma True` stubs, because a stub that proves
/// nothing while looking like a lemma is worse than an honest gap.

open FStar.List.Tot
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

/// Kleisli composition of denotations at a FIXED shape, where the producer's
/// outputs exactly match the consumer's inputs. This is the easy case of
/// sequencing, and it typechecks without any transport; the general case in
/// `denote` needs the residual handling described below.
let dseq (env:sig_env) (a b c:seg)
         (f:cdenote env ({ pre = a; post = b }))
         (g:cdenote env ({ pre = b; post = c }))
  : cdenote env ({ pre = a; post = c }) =
  fun r stk -> fbind (f r stk) (g r)

(* ------------------------------------------------------------------------ *)
(* The denotation function                                                  *)
(* ------------------------------------------------------------------------ *)

/// The meaning of a well-typed program.
///
/// NOT DEFINED. The definition is one clause per `term` constructor, each
/// reusing the corresponding M02 operation, with a single genuine difficulty:
/// the `TSeq` clause must transport along the residual segments that
/// `M03.compose` introduces, because the composite's shape is not
/// syntactically the shape of either operand. That transport needs
/// `append_assoc`, which is why `M03.lemma_compose_assoc` should be discharged
/// before this is attempted.
///
/// `assume val` rather than `val`: this is an admitted DEFINITION, and saying
/// so in the syntax keeps `grep assume` an accurate inventory of the gaps.
assume val denote (env:wenv) (t:term { well_typed env t })
  : Tot (cdenote env.w_ops (fst (Some?.v (infer env t))))

(* ------------------------------------------------------------------------ *)
(* T1: the empty program is the identity                                    *)
(* ------------------------------------------------------------------------ *)

/// This one is type-correct as stated, because `infer env TNil` reduces to
/// `Some (sid, pure_row)`.
///
/// ADMITTED: immediate once `denote` is defined.
let thm_denote_nil (env:wenv) (r:seg) (stk:vstack r)
  : Lemma (denote env TNil r stk == Pure stk) = admit ()

(* ------------------------------------------------------------------------ *)
(* Remaining obligations                                                    *)
(* ------------------------------------------------------------------------ *)

/// The theorems below are deliberately NOT written as F* lemmas yet: each
/// needs `denote` to exist, and most need a transport along the residual
/// segments, so writing them now would mean writing the transport before the
/// definition that motivates it. They are recorded here precisely enough to
/// be transcribed directly once `denote` lands.
///
/// T2  SEQUENCING IS KLEISLI COMPOSITION.
///     For well-typed `a`, `b` with `infer a = (sa, ea)`, `infer b = (sb, eb)`
///     and `compose sa sb = Some s`:
///         denote (TSeq a b) r  ==  denote a (rest_a @ r)  >=>  denote b (rest_b @ r)
///     where `rest_a`, `rest_b` are the residuals from `M03.unify sa.post
///     sb.pre`, at most one of which is non-empty (M03.lemma_unify_disjoint).
///     This is the central theorem: it licenses treating any word as a black
///     box given only its signature and row, which is what makes the
///     optimiser's DAG view sound and incremental re-checking correct.
///
/// T3  NATURALITY IN THE ROW.
///     For all `r`, `r'`, `x : vstack s.pre`, `y : vstack r`:
///         denote t (r @ r') (vappend x y)  relates to  denote t r x
///     by pushing `y` through unchanged. Follows from `lemma_frame_apply` by
///     induction on the term, and is the general form of "a word does not
///     disturb the stack beneath it".
///
/// T4  PURITY IS REAL.
///     If `is_pure env t` then `denote env t r stk` is `Pure _` for every `r`
///     and `stk` -- no `Op` node occurs anywhere in the tree. An effect system
///     that could not prove this would not be worth having.
///
/// T5  EFFECT-ROW SOUNDNESS.
///     If `infer env t = Some (_, row)` then `M04.within row (denote env t r stk)`
///     for every `r` and `stk`: the program performs no operation the type
///     system did not predict. The `THandle` case depends on M10.
///
/// T6  CAPABILITY SOUNDNESS.
///     No denotation duplicates a value of a non-copyable type or discards a
///     value of a non-droppable type. Formally: erasing to a multiset of leaf
///     values, a linear slot occurs exactly once in the output whenever it
///     occurred once in the input. This is what makes linearity a guarantee
///     about the SEMANTICS rather than merely a restriction on `M05.sop`.
