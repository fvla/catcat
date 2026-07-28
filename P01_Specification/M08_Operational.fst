module M08_Operational

/// catcat core specification, module 08: the abstract machine.
///
/// M07 says what a program MEANS; this module says how it RUNS. The split
/// matters because the two serve different consumers: the denotation is what
/// optimiser correctness is stated against, and the machine is what the
/// reference interpreter (P02) actually implements. M09 proves they agree, and
/// that agreement is the bridge from specification to implementation.
///
/// The machine is a continuation-passing stack machine with no return stack,
/// matching D01's decision to diverge from Forth on that point: control flow
/// is either static (juxtaposition, `case`) or handler-mediated, so there is
/// nothing for a return stack to hold.
///
/// STATUS: skeleton. State types are real; `step` is declared, not defined.

open FStar.List.Tot
open M01_Kinds
open M02_Stacks
open M03_Signatures
open M04_Effects
open M05_Terms
open M06_Typing

(* ------------------------------------------------------------------------ *)
(* Machine state                                                            *)
(* ------------------------------------------------------------------------ *)

/// A stack whose shape is packaged with it. The machine cannot be indexed by
/// a static shape -- that is the entire content of "running a program" -- so
/// the shape travels as data and M09's preservation theorem is what ties it
/// back to the static signature.
noeq type dstack =
  | DStack : shape:seg -> vstack shape -> dstack

/// The pending continuation: a program still to run. A list rather than a
/// tree, because juxtaposition is associative (M03) -- flattening is sound
/// precisely because of that law.
type kont = list term

noeq type mstate = {
  code : kont;
  stk  : dstack;
}

/// A machine that has stopped. Either it finished, or it is waiting on an
/// operation whose handler must supply the result -- the second case is how
/// effects suspend, and it is why the continuation is explicit here.
noeq type mresult (env:sig_env) =
  | MDone    : dstack -> mresult env
  | MEffect  : op:op_id -> vstack (env.op_of op).op_pre -> kont -> mresult env
  | MStuck   : mstate -> mresult env

(* ------------------------------------------------------------------------ *)
(* Transition relation                                                      *)
(* ------------------------------------------------------------------------ *)

/// One step of the machine.
///
/// NOT DEFINED. Each clause is short and mirrors the corresponding M02
/// operation; the only case with real content is `THandle`, which must push a
/// handler frame, and that frame's representation is fixed in M10. Defining
/// `step` before M10 settles would mean guessing that representation.
assume val step (env:wenv) (s:mstate) : Tot (either mstate (mresult env.w_ops))

/// Run to completion or to the fuel bound. Fuel keeps this total: catcat
/// programs may diverge, and the specification must not pretend otherwise.
/// The fuel-free statement is the coinductive one in M09.
assume val run (env:wenv) (fuel:nat) (s:mstate) : Tot (option (mresult env.w_ops))

(* ------------------------------------------------------------------------ *)
(* Obligations                                                              *)
(* ------------------------------------------------------------------------ *)

/// O1  DETERMINISM.
///     `step` is a function, so determinism is definitional. Recorded because
///     it is load-bearing for M09: agreement with a denotational semantics
///     would need far more care for a nondeterministic machine.
///
/// O2  PROGRESS (see M09).
///     A well-typed state never yields `MStuck`.
///
/// O3  PRESERVATION (see M09).
///     If a state is well typed at signature `s` and steps, the successor is
///     well typed at the residual of `s`.
///
/// O4  FUEL MONOTONICITY.
///     If `run env f s = Some r` then `run env f' s = Some r` for `f' >= f`.
///     Needed so that the fuel bound is an artefact of the specification and
///     never observable in a program's meaning.
