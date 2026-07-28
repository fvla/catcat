module R04_Erasure

/// P02, module 04: the bridge between the specification and the interpreter.
///
/// SUMMARY
///   `erase` maps P01's intrinsically typed stacks onto P02's runtime values.
///   The simulation obligation states that erasing commutes with running.
///
/// WHY THIS MODULE EXISTS
///   P01 and P02 use different representations on purpose. M02's `vstack` is
///   indexed by its shape, which makes ill-typed stacks unrepresentable and is
///   ideal for proving; it is also unrunnable, because the index would have to
///   survive to runtime. P02 erases the index and recovers the discipline as a
///   theorem.
///
///   Without this module the two phases are unrelated artefacts and every
///   correctness claim about the compiler is stated relative to nothing. This
///   is the same role M09's S5 plays for the denotational side, and the two
///   should be discharged together.
///
/// STATUS
///   `erase_value` and `erase_stack` are real and checked. The simulation
///   theorem is an obligation.

open FStar.List.Tot
open M01_Kinds
open M02_Stacks
open M03_Signatures
open M05_Terms
open M06_Typing
open R01_Runtime
open R02_Machine

(* ------------------------------------------------------------------------ *)
(* Erasure                                                                  *)
(* ------------------------------------------------------------------------ *)

val erase_value (#t:dtype) (v:value t) : Tot rvalue

val erase_stack (#s:seg) (st:vstack s) : Tot rstack

/// Erasure preserves length: the runtime stack has one slot per static slot.
/// Small, but it is the base case of the simulation argument and the reason
/// `take`/`give` line up with `vsplit`/`vappend`.
val lemma_erase_length (#s:seg) (st:vstack s)
  : Lemma (length (erase_stack st) == length s)

/// Erasure distributes over concatenation -- the runtime counterpart of
/// `M02.vappend`.
val lemma_erase_append (#a #r:seg) (x:vstack a) (y:vstack r)
  : Lemma (erase_stack (vappend x y) == give (erase_stack x) (erase_stack y))

(* ------------------------------------------------------------------------ *)
(* Obligations                                                              *)
(* ------------------------------------------------------------------------ *)

/// E1  SHAPE AGREEMENT.
///     For well-typed `t` with signature `s`, if the machine started on
///     `erase_stack st` terminates, the resulting stack has length
///     `length s.post + length r`. The runtime shape is the static shape.
///
/// E2  NO STUCK STATES.
///     For well-typed `t`, `step` never returns `SStuck`. Every `SStuck` case
///     in R02 is a shape or lookup failure that M06 has already excluded.
///
///     This is the obligation that earns the interpreter its keep as an
///     oracle, and it is also directly testable long before it is proved: a
///     fuzzer over well-typed terms that never observes `SStuck` is real
///     evidence, and one that does has found a genuine bug in either M06 or
///     R02.
///
/// E3  SIMULATION (the bridge theorem).
///     For well-typed `t` and every `r`, `st`:
///
///         run prelude fuel (load t (erase_stack st))  =  RDone (erase_stack v)
///           for some fuel
///       IFF
///         denote t r st  =  Pure v
///
///     and the machine suspends at `REffect op args` exactly when the
///     denotation is `Op op args k`.
///
///     Together with M09's S5 this closes the triangle: denotational
///     semantics, abstract machine, and running interpreter all agree. Every
///     compiler-correctness result in P04 is ultimately stated against this.
///
/// E4  SPECIALIZATION AGREEMENT.
///     Running `TSpecialize t` agrees with running `M11.specialize t d`. R02
///     currently implements `TSpecialize` by ignoring it and running the body,
///     which is only valid because of M11's E2 -- so this is where that
///     theorem first becomes empirically checkable rather than merely stated.
