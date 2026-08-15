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
/// STATUS: the fold `handle` is defined, in the D-36 shape, and agrees with the
/// machine R02 already implements -- but it lives in `M04_Effects` (D-59), since
/// M07's denotation needs it and an eliminator belongs with its type. What is
/// here is what that fold MEANS. The obligations H1-H5 remain prose.
///
/// WHAT IS DEFINED WHERE, so this module's shortness is not mistaken for
/// emptiness:
///
///   `M04.op_impl`     one operation's implementation, state on top (D-46)
///   `M04.handler`     the one record: effect handler = dictionary = class
///                     = module = Dictionary frame
///   `M04.handle`      the fold that interprets one effect away
///   `M04.id_handler`  the handler that changes nothing (H3's subject)
///   `M04.fwd_impl`    what an unimplemented operation does: forward outward
///
/// Everything below needs the typing judgment, which is why it could not move.

open FStar.List.Tot
open FStar.FunctionalExtensionality
open M01_Kinds
open M02_Stacks
open M03_Signatures
open M04_Effects
open M05_Terms
open M06_Typing

(* ------------------------------------------------------------------------ *)
(* One construct, five roles                                                *)
(* ------------------------------------------------------------------------ *)

/// `M04.handler` is simultaneously
///   * an effect handler,
///   * a typeclass dictionary,
///   * a class method table,
///   * a module implementation,
///   * a Dictionary frame overriding word meanings.
///
/// Not by analogy -- there is literally one type, and D03 explains why that
/// collapse is the design's best property rather than an overloading of terms.
/// `st` is what makes it a CLASS rather than merely a dispatch table: the state
/// segment is the instance's representation, each implementation is a method over
/// it, and D03 §3's `class ... over ( ... )` spelling is that record written in
/// surface syntax.
///
/// The claim now has a second witness beyond the type itself. M07's
/// `denote_static` gives `TWord w` the denotation `Op w`, so a word call and an
/// operation call are the SAME node of the free monad, and the ambient Dictionary
/// is the handler that interprets it (D-37, D-60). Resolving a word statically is
/// therefore `M04.handle` run at elaboration time -- which is exactly what M11's
/// `specialize` is, and why D-01 and D-02 are the same observation twice.

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
/// A DICTIONARY CARRIES BODIES (D-69). It used to be
///
///     { frames : list eff_id; stages : eff_id -> stage }
///
/// which names which effects are present and at what stage, and says nothing
/// about what any of them MEAN. `M11.specialize env d t` is supposed to resolve
/// `t`'s static effects against `d` and emit a residual — and with only a list
/// of ids to resolve against, there was nothing to resolve them TO. That was not
/// a small omission: it is why E3 could not be attempted, and it went unnoticed
/// because `specialize` was `assume val`, so nothing ever had to consume a
/// `dict`.
///
/// ONE TABLE FOR WORDS AND OPERATIONS, because `op_id` and `word_id` are one
/// namespace (D-01). Inlining a statically resolved word and inlining a static
/// effect's implementation are the same act on the same table, which is the
/// concrete form of "the Dictionary is a handler chain".
///
/// De-closured (D-45): `stages` was a function field, which every extractable
/// module is barred from and which `dict` had no reason to keep once it needed
/// to be built rather than merely described.
noeq type dict = {
  /// What a statically resolved word or operation is replaced BY.
  d_defs   : list (word_id & term);
  /// Which effects this dictionary resolves, and when.
  d_stages : list (eff_id & stage);
}

let empty_dict : dict = { d_defs = []; d_stages = [] }

let rec lookup_def (ds:list (word_id & term)) (w:word_id)
  : Tot (option term) (decreases ds) =
  match ds with
  | []            -> None
  | (w', t) :: r  -> if w' = w then Some t else lookup_def r w

let rec lookup_stage_of (ss:list (eff_id & stage)) (e:eff_id)
  : Tot (option stage) (decreases ss) =
  match ss with
  | []            -> None
  | (e', s) :: r  -> if e' = e then Some s else lookup_stage_of r e

let rec defs_bound_ops (ds:list (word_id & term)) (ops:list op_id)
  : Tot nat (decreases ops) =
  match ops with
  | []      -> 0
  | o :: r  -> mx (if Some? (lookup_def ds o) then o + 1 else 0)
                  (defs_bound_ops ds r)

/// One past the highest word `t` calls THAT THIS TABLE DEFINES. A word with no
/// entry in `ds` contributes nothing.
///
/// `M05.word_bound` is the same walk without the lookup, and the difference is
/// the point (D-81). That one counts every call; this one counts only the calls
/// `resolve_defs` will actually rewrite.
let rec defs_bound (ds:list (word_id & term)) (t:term)
  : Tot nat (decreases %[(term_size t <: nat); 0]) =
  match t with
  | TWord w               -> if Some? (lookup_def ds w) then w + 1 else 0
  | TSeq a b              -> mx (defs_bound ds a) (defs_bound ds b)
  | TDispatch ops _       -> defs_bound_ops ds ops
  | THandle _ _ i im b    -> mx (defs_bound ds i)
                                (mx (defs_bound_impls ds im) (defs_bound ds b))
  | TTry _ _ b c          -> mx (defs_bound ds b) (defs_bound ds c)
  | TSpecialize b         -> defs_bound ds b
  | _                     -> 0

and defs_bound_impls (ds:list (word_id & term)) (im:list (op_id & term))
  : Tot nat (decreases %[impls_size im; 1]) =
  match im with
  | []          -> 0
  | (_, t) :: r -> mx (defs_bound ds t) (defs_bound_impls ds r)


/// A dictionary is ORDERED when every definition calls only DEFINITIONS made
/// before it (D-70, weakened by D-81).
///
/// This is the well-foundedness `M11.specialize` runs on, and it is why that
/// function can exist at all. Inlining is `M05.inline_word` over the whole term
/// at once, so a pass that resolves every call to the highest DEFINED word in
/// `t` produces a term of strictly smaller `defs_bound` — each body substituted
/// in is ordered strictly below the word it defines — and the recursion is on
/// that measure. Nothing about the call graph has to be computed.
///
/// IT USED TO SAY `ordered_at w t`, i.e. every call, and that was stronger than
/// anything needed it to be. `resolve_defs` rewrites only what `lookup_def`
/// finds, so a call to something this table does not define — a `case` site's
/// operation, a declared effect's operation, a primitive — can sit at any id at
/// all without threatening completeness, let alone termination. The over-strict
/// version cost real expressiveness: it is what made a conditional inside a
/// generic body unrepresentable (D-80), because such a body calls the operations
/// its dispatch selects and those necessarily sit above an instance that was
/// named before its own contents existed.
///
/// A word that would break the ordering is not banned; it is marked `!Rec` and
/// left out of `d_defs`, so it is resolved at runtime by frame lookup instead
/// (D-67, D-70). `resolvable` below is what then refuses to call it static.
let dict_ordered (d:dict) : bool =
  for_all (fun (e:word_id & term) -> defs_bound d.d_defs (snd e) <= fst e) d.d_defs

/// A dictionary AGREES with an environment when every definition it carries has
/// the signature the environment records for that word.
///
/// This is D-69's second blocker written down. `M11.specialize` replaces a
/// `TWord w` — whose signature `M06.w_sig` reads out of `env` — by the body `d`
/// supplies, and E1 says the residual has the signature the original had. That
/// holds only if the body's own inferred signature IS `w_sig env w`; nothing
/// stated it, and nothing could, because `dict` had no bodies to state it about.
///
/// It is a hypothesis rather than a refinement on `dict` deliberately. A `dict`
/// is meaningful without an environment — it is a table of what words mean — and
/// tying the two together in the type would make every construction of one carry
/// a proof about the other. The environment is what a dictionary is CHECKED
/// against, so the check belongs where E1 is stated.
///
/// The ROW is not required to agree, and must not be: inlining a body brings its
/// effects with it, which is exactly what makes a static Dictionary word cost
/// nothing at runtime. Only the stack signature is invariant. That asymmetry is
/// the same asymmetry a Dictionary frame has: an override may perform effects
/// the word it replaces did not, which is the whole reason to install one.
let rec defs_agree (env:wenv) (ds:list (word_id & term)) : Tot bool (decreases ds) =
  match ds with
  | []           -> true
  | (w, t) :: r  -> (match infer env t with
                     | Some (s, _) -> s = w_sig env w && defs_agree env r
                     | None        -> false)

let dict_agrees (env:wenv) (d:dict) : bool = defs_agree env d.d_defs

/// Whether every effect in a row is resolvable in `d`, and at which stage.
/// The two-tier design of D04 lives in this one function: a `SStatic` effect
/// must be resolvable here at elaboration time, and a `SDynamic` one is
/// permitted to defer to a runtime frame.
let resolvable (d:dict) (row:erow) : bool =
  for_all (fun (e, _) -> Some? (lookup_stage_of d.d_stages e)) row

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
