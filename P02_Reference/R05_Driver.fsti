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
///
/// THE `kont` IN `REffect` IS NOT A LANGUAGE-LEVEL CONTINUATION, and the
/// distinction has to be stated here or it will be misread later.
///
/// No catcat program can name it. No `dtype` describes it. It is not reachable
/// from any value, it is never pushed, and nothing in D-36 is weakened by its
/// existence — a handler still never sees one. It is the *interpreter's own
/// machine state*, exposed for exactly one reason: `run` is a pure F* function
/// and cannot itself perform IO, so when an operation escapes every handler,
/// the only thing it can do is hand the host what it would need to carry on.
/// The host is the outermost handler, and `resume` is how it answers.
///
/// A COMPILED program has no such object. `print` compiles to a direct call
/// into the runtime, which returns; there is nothing to save and nothing to
/// resume. That this stays true is an obligation on the backend, not an
/// intention — it is what "the semantics must be optimized out" means, and
/// the place it could quietly stop being true is a backend that implements
/// built-in effects by reusing this driver's shape.
noeq type rresult =
  | RDone       : rstack -> rresult
  | REffect     : op_id -> rstack -> kont -> rresult
  | RStuck      : string -> rresult
  | ROutOfFuel  : rresult

(* ------------------------------------------------------------------------ *)
(* Running                                                                  *)
(* ------------------------------------------------------------------------ *)

val run (d:rdict) (fuel:nat) (s:mstate) : Tot rresult

val eval (d:rdict) (fuel:nat) (t:term) (init:rstack) : Tot rresult

/// Carry on from an escaped operation, with `stk` as the stack the host leaves
/// behind: the operation's arguments removed and its results pushed.
///
/// The host performs the operation itself, so this is the outermost handler
/// implemented outside the language — category 2 of the effect design, the one
/// only the compiler or interpreter can supply.
val resume (d:rdict) (fuel:nat) (k:kont) (stk:rstack) : Tot rresult

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
