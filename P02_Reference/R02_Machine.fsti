module R02_Machine

/// P02, module 02: the abstract machine.
///
/// SUMMARY
///   A defunctionalised stack machine. State is a continuation (a list of
///   frames) plus a stack; `step` is one transition. This is the executable
///   form of M08.
///
/// WHY DEFUNCTIONALISED
///   This is the single most important decision in P02, and it is forced by
///   the self-hosting goal rather than chosen for elegance.
///
///   The obvious way to write an interpreter for a free monad is to let the
///   continuation be an F* closure. That extracts to OCaml fine and to catcat
///   NOT AT ALL: catcat has no runtime function values (D02 6). So the
///   continuation is represented as DATA -- a `list kframe` -- and every
///   transition is a first-order rewrite of that data.
///
///   The pleasant consequence is that deep handlers become easy rather than
///   hard. A handler needs the rest of the computation; here the rest of the
///   computation is literally a value in scope, so "reentrant by construction"
///   (D03 2) is a property of the representation instead of something to
///   arrange.
///
///   M08 already anticipated this by making `kont` a list rather than a tree,
///   which is sound because juxtaposition is associative (M03).
///
/// NO RETURN STACK
///   Per D01, control flow is either static or handler-mediated, so there is
///   nothing a return stack would hold. `kframe` is the whole control state.

open FStar.List.Tot
open M01_Kinds
open M04_Effects
open M05_Terms
open R01_Runtime

(* ------------------------------------------------------------------------ *)
(* Continuations                                                            *)
(* ------------------------------------------------------------------------ *)

/// A continuation frame.
///
///   `KTerm t`             -- code still to run
///   `KHandler e impls st` -- an active handler boundary carrying its state;
///                            popped when the body beneath it completes, at
///                            which point the state is pushed onto the stack
///   `KInit e n impls b`   -- waiting for an initialiser to finish, so its `n`
///                            results can be moved into a fresh handler frame
///   `KRestore e op n`     -- waiting for an implementation to finish, so its
///                            top `n` values can be moved back into the frame
///
/// The handler frame is what makes the chain searchable at the point an
/// operation is invoked, which is how D04's Dictionary lookup works at runtime.
///
/// STATE LIVES IN THE FRAME, NOT ON THE STACK (D-36). A handler is a stateful
/// object; its state has to survive across operation calls and be reachable at
/// a depth the body cannot know, so the stack is the one place it cannot live.
/// `KInit` and `KRestore` exist only to move it in and out, and both are
/// ordinary frames — nothing here captures a continuation.
///
/// `KHandler`'s state is an OPTION because it is BORROWED while an
/// implementation runs. See `step`: re-entering a handler whose state is out on
/// loan is reported rather than served with a stale copy.
noeq type kframe =
  | KTerm    : term -> kframe
  | KHandler : eff_id -> list (op_id & term) -> option rstack -> kframe
  | KInit    : eff_id -> nat -> list (op_id & term) -> term -> kframe
  | KRestore : eff_id -> op_id -> nat -> kframe

type kont = list kframe

noeq type mstate = {
  code : kont;
  stk  : rstack;
}

/// Outcome of a single transition.
///
///   `SNext`   -- ordinary progress
///   `SDone`   -- the continuation is exhausted; the stack is the result
///   `SEffect` -- an operation escaped every handler. For a well-typed whole
///                program this means an unhandled effect at the top level,
///                which is a legitimate outcome (that is what `!IO` at `main`
///                means), not an error.
///   `SStuck`  -- a shape or lookup failure. Unreachable for well-typed
///                programs; that unreachability is R04's obligation E2, and
///                keeping the case explicit is what makes it testable.
noeq type sresult =
  | SNext   : mstate -> sresult
  | SDone   : rstack -> sresult
  | SEffect : op_id -> rstack -> kont -> sresult
  | SStuck  : string -> sresult

(* ------------------------------------------------------------------------ *)
(* Handler resolution                                                       *)
(* ------------------------------------------------------------------------ *)

/// Walk the continuation outward for the nearest handler of `e` implementing
/// `op`. Returns the implementation and that frame's state, which is `None`
/// when the state is currently borrowed by a running implementation.
///
/// The implementation runs with the frame STILL INSTALLED, which is the whole
/// of "every effect is reentrant" (D03 §2) and costs nothing — no continuation
/// is captured, extracted or resumed.
val find_handler (k:kont) (e:eff_id) (op:op_id)
  : Tot (option (term & option rstack))

/// Replace the state of the frame `find_handler` would select. The two walk
/// the chain by the same rule, and must keep doing so: a divergence would put
/// the state back into a different handler from the one that lent it.
val set_handler_state (k:kont) (e:eff_id) (op:op_id) (st:option rstack)
  : Tot kont

(* ------------------------------------------------------------------------ *)
(* Transition                                                               *)
(* ------------------------------------------------------------------------ *)

/// Load a program into an initial state.
val load (t:term) (s:rstack) : Tot mstate

/// One step. Total: every case is covered, including the ill-shaped ones,
/// because a reference interpreter that could get stuck without saying so
/// would be useless as an oracle.
val step (d:rdict) (s:mstate) : Tot sresult
