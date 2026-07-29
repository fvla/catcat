module R05_Driver

/// P02, module 05: the run loop and entry points.
///
/// SUMMARY
///   Fuel-bounded evaluation, result rendering, and a few example programs
///   used as the executable smoke test until P03's parser exists.
///
/// WHY FUEL
///   catcat programs may diverge, and a total specification must not pretend
///   otherwise. Fuel keeps `run` total in F*; `ROutOfFuel` is an artefact of
///   the specification and must never be observable in a program's meaning,
///   which is M08's obligation O4.

open FStar.List.Tot
open M01_Kinds
open M04_Effects
open M05_Terms
open R01_Runtime
open R02_Machine
open R03_Prelude

(* ------------------------------------------------------------------------ *)
(* Results                                                                  *)
(* ------------------------------------------------------------------------ *)

/// `REffect` is a legitimate outcome, not a failure: an unhandled effect at
/// the top level is what `!IO` on `main` means. `RStuck` is the only genuine
/// error, and R04's obligation E2 says it is unreachable for well-typed input.
noeq type rresult =
  | RDone       : rstack -> rresult
  | REffect     : op_id -> rstack -> rresult
  | RStuck      : string -> rresult
  | ROutOfFuel  : rresult

(* ------------------------------------------------------------------------ *)
(* Running                                                                  *)
(* ------------------------------------------------------------------------ *)

val run (d:rdict) (fuel:nat) (s:mstate) : Tot rresult

val eval (d:rdict) (fuel:nat) (t:term) (init:rstack) : Tot rresult

/// Evaluate against the standard dictionary on an empty stack.
val eval_prelude (fuel:nat) (t:term) : Tot rresult

(* ------------------------------------------------------------------------ *)
(* Rendering                                                                *)
(* ------------------------------------------------------------------------ *)

val render_value  (v:rvalue) : Tot string
val render_stack  (s:rstack) : Tot string
val render_result (r:rresult) : Tot string

(* ------------------------------------------------------------------------ *)
(* Examples                                                                 *)
(* ------------------------------------------------------------------------ *)

/// `2 3 add 4 mul` => 20. Exercises literals, primitives, and juxtaposition.
val ex_arith : term

/// A sealed counter, following D03 3: pack an i64, increment through the
/// boundary, unpack. Exercises `TPack`/`TUnpack` and demonstrates that the
/// class boundary has no runtime representation beyond the wrapper.
val ex_counter : term

/// Sum introduction and elimination. Exercises the one construct that cannot
/// be encoded as a stack segment (D01 3.1).
val ex_sum : term

/// `prelude` extended with the demo effect operation the handler examples use.
/// The smoke test runs everything against this, since `prelude` alone would
/// leave `ex_handled` with an unbound word.
val demo_dict : rdict

/// An effect operation resolved by an enclosing handler, then the same
/// operation escaping to the top level. Exercises the Dictionary walk of
/// D04 2 and shows both handled and unhandled outcomes.
val ex_handled   : term

/// A stateful handler: `ask` returns a running count and leaves it
/// incremented. The state lives in the handler frame and is threaded through
/// the implementation's own signature (D-36) — no continuation is captured.
val ex_stateful  : term
val ex_unhandled : term

/// `List[i64]` built as `[7, 9]`, from the inside out via `TRoll`/`TBoxNew`.
/// The recursive type this needs -- a sum variant referring to itself -- was
/// inexpressible before pointer types; it is well-formed now only because the
/// self-reference passes through `TBox` (see M01's `wf_dtype`).
val ex_list : term

/// Every example paired with its name, for the smoke test.
val examples : list (string & term)
