module M09_Soundness

/// catcat core specification, module 09: soundness.
///
/// Two families of theorem live here.
///
/// The first is ordinary type soundness -- progress and preservation for the
/// M08 machine. Much of it is cheap: because M02 stacks are intrinsically
/// typed, "the stack has the shape the signature says" is not a theorem at all
/// but a property of the representation. What remains is genuinely about the
/// language: that capability checks are never circumvented, and that the
/// effect row over-approximates what actually happens.
///
/// The second is the agreement theorem between M07 and M08. This is the most
/// valuable result in the specification, because it is what makes the
/// reference interpreter a witness for the denotational semantics that
/// compiler correctness is stated against. Without it the two halves of the
/// project are unrelated artefacts.
///
/// STATUS: skeleton. Obligations recorded; nothing proved.

open FStar.List.Tot
open M01_Kinds
open M02_Stacks
open M03_Signatures
open M04_Effects
open M05_Terms
open M06_Typing
open M07_Denotation
open M08_Operational

(* ------------------------------------------------------------------------ *)
(* Well-typed machine states                                                *)
(* ------------------------------------------------------------------------ *)

/// A machine state is well typed at `s` when its pending code, run against
/// its current stack, has signature `s`. The definition is short but depends
/// on `M08.step`'s handler-frame representation, so it is declared here and
/// pinned down alongside M10.
assume val state_typed (env:wenv) (st:mstate) (s:srow) : Tot bool

(* ------------------------------------------------------------------------ *)
(* Obligations                                                              *)
(* ------------------------------------------------------------------------ *)

/// S1  PROGRESS.
///     If `state_typed env st s` then `step env st` is not `Inr (MStuck _)`.
///     A well-typed program either takes a step, finishes, or suspends on an
///     operation -- it never jams. Note the third disjunct: suspension is a
///     normal outcome here, unlike in a language without effects, and any
///     progress statement that omitted it would be false.
///
/// S2  PRESERVATION.
///     If `state_typed env st s` and `step env st = Inl st'` then
///     `state_typed env st' s'` where `s'` is the residual of `s` after the
///     step. Cheap for the stack component (M02 makes shape errors
///     unrepresentable), real work for the continuation and handler frames.
///
/// S3  CAPABILITY SOUNDNESS.
///     No reachable state duplicates a value at a type lacking `CCopy`, nor
///     discards one at a type lacking `CDrop`. Together with M07's T6 this is
///     the linear type system's actual guarantee, and the reason `delete` in
///     the Counter example of D03 means something that `pop` does not.
///
/// S4  EFFECT SOUNDNESS.
///     If `infer env t = Some (_, row)` then every `MEffect op _ _` reachable
///     from `t` has `env.w_ops.eff_of op` present in `row`. The runtime
///     counterpart of M07's T5.
///
/// S5  AGREEMENT (the bridge theorem).
///     For well-typed `t` and every `r`, `stk`:
///
///         run env fuel { code = [t]; stk = DStack _ stk }
///
///     converges to `MDone (DStack _ v)` for some fuel
///       IFF  `denote env t r stk` is `Pure v`;
///
///     and it suspends at `MEffect op arg k`
///       IFF  `denote env t r stk` is `Op op arg k'` with `k` and `k'`
///            denoting the same continuation.
///
///     This is the theorem that makes P02's interpreter a witness for M07,
///     and therefore the theorem every compiler-correctness result in P04 is
///     ultimately stated relative to. Discharge order: T2 (M07) first, since
///     agreement on `TSeq` is where the induction does its work.
///
/// S6  TOTALITY OF TYPE CHECKING.
///     `M06.infer` is a total function, so type checking always terminates.
///     Already true by construction -- `infer` is `Tot` -- and recorded only
///     because D01 leans on it when claiming a real-time language server is
///     achievable.
