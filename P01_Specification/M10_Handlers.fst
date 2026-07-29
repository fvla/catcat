module M10_Handlers

/// catcat core specification, module 10: handlers, interfaces, classes, the
/// Dictionary.
///
/// This module is where D03's central claim is cashed out: effects,
/// interfaces, traits, classes, modules and the Dictionary are ONE construct,
/// distinguished only by when the handler is resolved and whether it is
/// erased. Every definition below is shared by all of them.
///
/// HANDLERS DO NOT CAPTURE CONTINUATIONS (D-36). An operation call runs an
/// implementation, which returns; the handler carries state threaded through
/// its own implementations' signatures. "Every effect is reentrant" is the
/// installed-frame property -- `R02.step` runs an implementation with the
/// handler frame still in the continuation -- not deep-handler semantics.
///
/// The `op_impl` below is still the DEEP shape, taking the continuation. It is
/// the one place in the project that has not caught up with D-36 yet, because
/// it is only reachable from `handle`, which is `assume val`. Narrowing it to
/// `vstack o.op_pre -> free env a` and adding the state segment to `handler`
/// is what the definition of `handle` will require; M06's `THandle` rule and
/// R02's machine already work the corrected way, so this is a gap in the
/// denotational side alone.
///
/// STATUS: skeleton. Types are real; `handle` is declared, not defined.

open FStar.List.Tot
open M01_Kinds
open M02_Stacks
open M03_Signatures
open M04_Effects
open M05_Terms
open M06_Typing

(* ------------------------------------------------------------------------ *)
(* Handlers                                                                 *)
(* ------------------------------------------------------------------------ *)

/// An implementation of a single operation. It receives the operation's
/// arguments AND the continuation expecting the operation's results, which is
/// what makes the handler deep.
type op_impl (env:sig_env) (o:op_sig) (a:seg) =
    vstack o.op_pre
  -> (vstack o.op_post -> free env a)
  -> free env a

/// A handler for one effect: an implementation per operation, plus a return
/// clause. This record is simultaneously
///   * an effect handler,
///   * a typeclass dictionary,
///   * a class method table,
///   * a module implementation,
///   * a Dictionary frame overriding word meanings.
/// Not by analogy -- there is literally one type, and D03 explains why that
/// collapse is the design's best property rather than an overloading of terms.
noeq type handler (env:sig_env) (eff:eff_id) (a:seg) = {
  h_ops : op:op_id -> op_impl env (op_of env op) a;
  h_ret : vstack a -> free env a;
}

/// Interpret away one effect.
///
/// NOT DEFINED. The definition is a fold over `M04.free`: `Pure` goes to
/// `h_ret`, an `Op` belonging to `eff` goes to the matching `h_ops` entry with
/// the recursively handled continuation, and any other `Op` is forwarded
/// unchanged. The recursion is on the free structure and terminates for the
/// same reason `fbind` does.
assume val handle (#env:sig_env) (#eff:eff_id) (#a:seg)
                  (h:handler env eff a) (m:free env a)
  : Tot (free env a)

(* ------------------------------------------------------------------------ *)
(* The Dictionary                                                           *)
(* ------------------------------------------------------------------------ *)

/// The ambient chain of handlers. A `use` declaration, a class instantiation,
/// an interface implementation and an explicit `handle` block all push a frame
/// onto this chain; lookup walks it from the innermost frame outward.
///
/// Because modules are Dictionary handlers (D04), swapping an entire module
/// for a reinterpreted one -- the SIMD-functor example from the draft -- is
/// pushing one frame, not a separate language feature.
noeq type dict (env:sig_env) = {
  frames : list eff_id;
  stages : eff_id -> stage;
}

/// Whether every effect in a row is resolvable in `d`, and at which stage.
/// The two-tier design of D04 lives in this one function: a `SStatic` effect
/// must be resolvable here at elaboration time, and a `SDynamic` one is
/// permitted to defer to a runtime frame.
let resolvable (#env:sig_env) (d:dict env) (row:erow) : bool =
  for_all (fun (e, _) -> mem e d.frames) row

(* ------------------------------------------------------------------------ *)
(* Obligations                                                              *)
(* ------------------------------------------------------------------------ *)

/// H1  HANDLING DISCHARGES.
///     If `within row m` and `eff` is in `row`, then
///     `within (row_remove eff row) (handle h m)` provided the handler's own
///     implementations stay inside `row_remove eff row`. This is the semantic
///     counterpart of M06's `THandle` rule, and the reason a handled program
///     can be genuinely pure.
///
/// H2  HANDLING IS A MONAD MORPHISM.
///     `handle h (fbind m f) == fbind (handle h m) (fun v -> handle h (f v))`
///     when `f` introduces no operations of `eff`. This is what lets the
///     optimiser move code across a handler boundary, and it is the property
///     most likely to be quietly violated by an efficient implementation --
///     worth proving early for that reason.
///
/// H3  IDENTITY HANDLER.
///     The handler whose implementations re-perform their operation and whose
///     return clause is `Pure` satisfies `handle h m == m`. A sanity check
///     that the fold is not lossy.
///
/// H4  SEALING IS FREE.
///     `M02.vseal` and `M02.vunseal` are mutually inverse
///     (`M02.lemma_unseal_seal` already proves one direction), so a class
///     boundary has no runtime representation. Combined with M11's erasure
///     theorem, this is why the object model of D03 costs nothing: a method
///     call through a statically resolved interface compiles to the same code
///     as a direct call.
///
/// H5  CAPABILITY NARROWING IS SOUND.
///     A sealed type exposing fewer capabilities than its representation
///     cannot have the missing ones recovered by any client, since `TUnpack`
///     is well typed only inside the class body. This is what makes a linear
///     `Counter` over a copyable `int` an actual guarantee.
