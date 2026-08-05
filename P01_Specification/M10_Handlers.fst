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
/// STATUS: `handle` is now defined, in the D-36 shape, and agrees with the
/// machine R02 already implements. The obligations H1-H5 remain prose.

open FStar.List.Tot
open FStar.FunctionalExtensionality
open M01_Kinds
open M02_Stacks
open M03_Signatures
open M04_Effects
open M05_Terms
open M06_Typing

(* ------------------------------------------------------------------------ *)
(* Handlers                                                                 *)
(* ------------------------------------------------------------------------ *)

/// An implementation of a single operation, under D-36: it receives the
/// handler's state on top of the operation's arguments, and returns the updated
/// state on top of the operation's results. No continuation appears, and there
/// is nowhere one could be smuggled in -- the type is a plain stack transformer
/// in the free monad, so an implementation can perform effects of its own but
/// cannot see, duplicate or discard the rest of the program.
///
/// STATE ON TOP, not underneath (D-46). This is forced rather than chosen: the
/// runtime dictionary records which effect an operation belongs to and not its
/// arity, so the machine cannot splice state in beneath the arguments. It reads
/// correctly anyway, the receiver being pushed last.
type op_impl (env:sig_env) (st:seg) (o:op_sig) =
  vstack (st @ o.op_pre) -> free env (st @ o.op_post)

/// A handler for one effect: a state segment and an implementation per
/// operation. This record is simultaneously
///   * an effect handler,
///   * a typeclass dictionary,
///   * a class method table,
///   * a module implementation,
///   * a Dictionary frame overriding word meanings.
/// Not by analogy -- there is literally one type, and D03 explains why that
/// collapse is the design's best property rather than an overloading of terms.
///
/// The state segment is what makes a handler a CLASS rather than merely a
/// dispatch table: `st` is the instance's representation, each implementation
/// is a method over it, and D03 §3's `class ... over ( ... )` spelling is this
/// type written in surface syntax. A stateless handler is `st = []`, so
/// nothing needs a separate rule.
///
/// `h_ops` is a function field, which every extractable module in this project
/// is forbidden (D-20). M10 is not extracted and nothing constructs a `handler`
/// outside the specification, so the closure is confined to the denotational
/// side; the table is dependently typed per operation, so de-closuring it the
/// way D-45 de-closured `sig_env` would need an existential rather than a list.
noeq type handler (env:sig_env) (eff:eff_id) (st:seg) = {
  h_ops : op:op_id -> op_impl env st (op_of env op);
}

/// Interpret away one effect.
///
/// A fold over `M04.free` carrying the handler state. `Pure` returns the state
/// on top of the body's results -- which is why M06's `THandle` rule gives the
/// composite the signature `( s.pre -- st @ s.post )`, and why `handle Counter
/// over ( i64 ) init { 0 } { ... } { tick tick + }` leaves `1 2` and not `1`.
/// An operation of `eff` runs its implementation, whose result is split back
/// into the new state and the operation's results; anything else is forwarded
/// with the handler still wrapped around the tail.
///
/// That forwarding clause is where reentrancy lives. The handler is still
/// installed around `k res`, so an operation performed by the continuation --
/// including one performed by an implementation, since an implementation's own
/// effects are part of the tree it returns -- reaches this same handler. No
/// continuation was captured to achieve it.
let rec handle (#env:sig_env) (#eff:eff_id) (#st:seg) (#a:seg)
               (h:handler env eff st) (state:vstack st) (m:free env a)
  : Tot (free env (st @ a)) (decreases m) =
  match m with
  | Pure v      -> Pure (vappend state v)
  | Op op arg k ->
    if eff_of env op = eff
    then fbind (h.h_ops op (vappend state arg))
               (fun r -> let (state', res) = vsplit st r in
                      handle h state' (k res))
    else Op op arg (on _ (fun res -> handle h state (k res)))

/// The handler that changes nothing: no state, every implementation
/// re-performing its own operation. H3 below is the statement that handling
/// with it is the identity, which is the sanity check that the fold loses
/// nothing -- and note it typechecks only because the state segment is `[]`,
/// so `handle`'s result shape `[] @ a` is `a` on the nose.
let id_handler (env:sig_env) (eff:eff_id) : handler env eff [] =
  { h_ops = (fun op -> fun args -> Op op args (on _ Pure)) }

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
///     `within (row_remove eff row) (handle h state m)` provided every
///     implementation's own result satisfies `within (row_remove eff row)`.
///     This is the semantic counterpart of M06's `THandle` rule, and the reason
///     a handled program can be genuinely pure. Note the proviso is a real
///     restriction and not bookkeeping: an implementation that performs its own
///     effect reaches the enclosing handler chain, so a handler for `eff` whose
///     implementation performs `eff` does NOT discharge it -- which is exactly
///     the reentrancy the design wants, and exactly why the row cannot be
///     narrowed unconditionally.
///
/// H2  HANDLING IS A MONAD MORPHISM.
///     `handle h state (fbind m f)` relates to `handle h state m` followed by
///     `handle h` at the resulting state, when `f` introduces no operations of
///     `eff`. Stating it precisely needs the state to be threaded through the
///     equation -- `handle` returns `st @ a`, so the composite splits the state
///     back off before continuing -- which is the one place the D-36 shape makes
///     a law wordier than the deep-handler version would have been. It is what
///     lets the optimiser move code across a handler boundary, and it is the
///     property most likely to be quietly violated by an efficient
///     implementation.
///
/// H3  IDENTITY HANDLER.
///     `handle (id_handler env eff) VNil m == m`, where `id_handler` is the
///     stateless handler whose implementations re-perform their operation. A
///     sanity check that the fold is not lossy.
///
///     Both `Op` cases need `M04`'s continuation congruence, and neither can
///     use the trick that made the monad laws provable: that trick works by
///     applying a helper to a literal `Op` node so F* reduces by conversion,
///     and `handle`'s `Op` case is guarded by `eff_of env op = eff`, which
///     conversion cannot decide. Discharging H3 therefore wants an `Op`
///     congruence stated over PROJECTED continuations, whose dependent type
///     mentions `Op?.op` of the term being projected -- so it needs the
///     projection to typecheck against a propositional equation rather than a
///     definitional one. That is the missing piece, and it is shared with H2.
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
///     cannot have the missing ones recovered by any client, since `PUnpack`
///     is well typed only inside the class body. This is what makes a linear
///     `Counter` over a copyable `int` an actual guarantee.
