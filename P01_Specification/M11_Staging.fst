module M11_Staging

/// catcat core specification, module 11: staging, specialization, and JIT.
///
/// This module carries the project's two critical goals (D01): manual JIT, and
/// metacompiler functionality. It gets both from ONE operation.
///
/// The observation that makes this work is that compile-time specialization
/// and runtime JIT differ only in WHEN they run:
///
///   * `specialize p d` at elaboration time resolves `p`'s static effects
///     against the ambient dictionary and emits a residual program. Because
///     the resolved effects are erased, the abstraction costs nothing at
///     runtime -- the requirement D04 states as non-negotiable.
///
///   * `specialize p d` at runtime, with `d` supplied by the running program,
///     IS the JIT. The draft's "a JIT function is a function with user-defined
///     effects instantiated at runtime" is exactly this, and it is why JIT is
///     not a separate subsystem here.
///
/// One operation, one correctness theorem (E2), two call sites. The nearest
/// prior art is "Collapsing Towers of Interpreters" (Amin & Rompf, POPL 2018),
/// which treats a tower of interpreters staged so the levels cost nothing;
/// D04 records what catcat takes from it and where it diverges.
///
/// STATUS: `specialize` is DEFINED (D-74) -- one downward pass over the id
/// space, inlining every statically resolvable word. What remains assumed is
/// `specialize_typed`, and E1-E7 remain obligations. The reflective-tower
/// interface is real; two of `stage_req`'s four answers are unreachable and say
/// so.

open FStar.List.Tot
open M01_Kinds
open M02_Stacks
open M03_Signatures
open M04_Effects
open M05_Terms
open M06_Typing
open M07_Denotation
open M10_Handlers

(* ------------------------------------------------------------------------ *)
(* Specialization                                                           *)
(* ------------------------------------------------------------------------ *)

/// One downward pass over the id space: resolve word `n-1`, then `n-2`, and so
/// on to 0.
///
/// THE ORDERING IS THE ALGORITHM (D-70). A word calls only words defined before
/// it, so a body spliced in at step `w` mentions only words `< w` — every one of
/// which a later step still has to visit. Descending is therefore enough; no
/// worklist, no fixpoint, and no check that the substitution settled.
///
/// TERMINATION IS ON THE FUEL, NOT ON THE TERM, and that is a choice worth
/// naming. Recursing on `M05.word_bound` of the residual would be tighter and
/// would need a lemma — that inlining the highest word strictly lowers the
/// bound — which is true only when `dict_ordered d`. Counting down instead makes
/// the function total for ANY dictionary, and turns a disordered one from a
/// divergence into an incompleteness: inlining a self-referential body at step
/// `w` leaves the inner `TWord w` behind, because the pass has already gone past
/// `w` and never returns. A specializer that quietly leaves a call is a residual
/// that still runs; one that loops is not.
///
/// The cost is a pass per id rather than per call. This is a specification: the
/// implementation walks the term once with the table in hand, and agreeing with
/// this is its obligation.
let rec resolve_below (d:dict) (n:nat) (t:term) : Tot term (decreases n) =
  if n = 0 then t
  else
    let w : word_id = n - 1 in
    let t' = (match lookup_def d.d_defs w with
              | None      -> t
              | Some body -> inline_word w body t) in
    resolve_below d (n - 1) t'

/// Resolve every statically-staged effect of `t` against `d`, producing a
/// residual program.
///
/// DEFINED, at last, and the reason it could not be before is worth keeping in
/// view: it needed a dictionary with bodies (D-69) and a termination measure
/// (D-70), and neither was a proof difficulty. `M05.word_bound t` bounds the
/// words `t` can call, so that many steps suffice.
///
/// WHAT IT DOES: inline every statically resolvable word. That is less than the
/// partial evaluator this comment used to promise and it is the whole of the
/// first clause, which is the one that matters — `denote_static` gives `TWord w`
/// the denotation `Op w` (D-60), so inlining a resolved word IS `M04.handle`
/// applied to the Dictionary frame, run at elaboration time. Which words are
/// resolvable is entirely `d`'s business: a recursive word is marked `!Rec` and
/// left out of `d_defs` (D-67, D-70), a dynamic effect's operation was never in
/// it, and a prelude primitive has no body to inline.
///
/// WHAT IT DOES NOT DO, each for a stated reason rather than for want of effort:
///
///   * Fold a dispatch on a known tag. `TDispatch` selects on a runtime value;
///     folding it needs the scrutinee to be a literal `PInj`, which is a
///     constant-propagation pass over `TSeq` and is genuinely separate work.
///   * Erase `PPack`/`PUnpack`. Sound by M10's H4, which is not proved.
///   * DISCHARGE A `TSpecialize` NODE. E2's domain constraint says it must, and
///     it does not, and the dependency is real rather than an oversight:
///     stripping the marker is honest only when the body has no static effect
///     left, which is a question about `infer` of the RESIDUAL, and knowing the
///     residual is even well typed is E1. So E1 comes first, and until then a
///     `TSpecialize` is passed through — visible in the output rather than
///     silently discarded, which is the failure mode to prefer.
///
/// The `well_typed` refinement is not consumed. It is kept because E1, E2 and E3
/// are all stated at it and a signature change here would ripple through three
/// obligation types for no gain.
let specialize (env:wenv) (d:dict) (t:term { well_typed env t }) : Tot term =
  resolve_below d (word_bound t) t

/// A dictionary with nothing in it changes nothing. The sanity check that the
/// pass is doing lookup rather than rewriting, and the one property of
/// `resolve_below` that needs no ordering hypothesis.
let rec lemma_resolve_below_empty (d:dict { Nil? d.d_defs }) (n:nat) (t:term)
  : Lemma (ensures resolve_below d n t == t) (decreases n) =
  if n = 0 then () else lemma_resolve_below_empty d (n - 1) t

let lemma_specialize_empty (env:wenv) (t:term { well_typed env t })
  : Lemma (specialize env empty_dict t == t) =
  lemma_resolve_below_empty empty_dict (word_bound t) t

(* --- non-vacuity: the pass computes --------------------------------------- *)

/// An ordered dictionary: word 7 is `3 4`, word 5 is `2`. Both bodies call only
/// words below their own id, which is `M05.ordered_at` and hence
/// `M10.dict_ordered`.
let ex_defs : dict =
  { d_defs = [ (7, TSeq (TWord 3) (TWord 4))
             ; (5, TWord 2) ];
    d_stages = [] }

let lemma_ex_defs_ordered () : Lemma (dict_ordered ex_defs) =
  assert_norm (dict_ordered ex_defs)

/// A word is replaced by its body; a word with no definition is left alone.
let lemma_specialize_inlines ()
  : Lemma (resolve_below ex_defs 8 (TSeq (TWord 7) (TWord 1))
           == TSeq (TSeq (TWord 3) (TWord 4)) (TWord 1)) =
  assert_norm (resolve_below ex_defs 8 (TSeq (TWord 7) (TWord 1))
               == TSeq (TSeq (TWord 3) (TWord 4)) (TWord 1))

/// ONE PASS RESOLVES A CHAIN, which is the whole content of D-70 as an
/// algorithm. Word 7 is `6`, word 6 is `5`, word 5 is `2`, so the chain runs
/// DOWNWARD in id — which is not a convenience of the example but what
/// `dict_ordered` forces. Descending meets each link after the one that
/// introduces it, so `7` resolves all the way to `2` in a single sweep, with no
/// worklist and no test that the substitution settled.
let ex_chain : dict =
  { d_defs = [(7, TWord 6); (6, TWord 5); (5, TWord 2)]; d_stages = [] }

let lemma_ex_chain_ordered () : Lemma (dict_ordered ex_chain) =
  assert_norm (dict_ordered ex_chain)

let lemma_specialize_chain ()
  : Lemma (resolve_below ex_chain 8 (TWord 7) == TWord 2) =
  assert_norm (resolve_below ex_chain 8 (TWord 7) == TWord 2)

/// AND THE CONVERSE, kept because it is the property that makes the fuel
/// formulation the right one. Reverse the chain so word 5 calls word 7 — which
/// `dict_ordered` refuses — and the pass terminates anyway, leaving a call
/// behind: step 7 runs before anything introduces `TWord 7`, so nothing resolves
/// it. Incompleteness, not divergence.
let ex_unordered : dict =
  { d_defs = [(5, TWord 7); (7, TWord 2)]; d_stages = [] }

let lemma_ex_unordered_is_unordered () : Lemma (not (dict_ordered ex_unordered)) =
  assert_norm (not (dict_ordered ex_unordered))

let lemma_specialize_unordered_leaves_a_call ()
  : Lemma (resolve_below ex_unordered 8 (TWord 5) == TWord 7) =
  assert_norm (resolve_below ex_unordered 8 (TWord 5) == TWord 7)

/// The residual is still well typed, with the static effects gone. Stated
/// separately from E2 because the compiler needs it long before anyone proves
/// semantic preservation, and because M06's `lemma_static_specializes_to_pure`
/// already establishes the type-level half.
///
/// STILL ASSUMED, and the hypothesis it needs is now writable where it was not.
/// Discharging it requires `M10.dict_agrees env d` — every body in `d` has the
/// signature `env` records for its word — and then an induction over
/// `resolve_below`: each step replaces `TWord w`, whose signature `infer` reads
/// as `w_sig env w`, by a body of that same signature, so `M06.compose` sees the
/// same operands at every enclosing `TSeq`. The `THandle` case additionally
/// needs `op_of env.w_ops` unchanged, which holds because `inline_word_impls`
/// does not rewrite an implementation's key — the same fact E7 relies on for
/// `subst_words`. Nothing here is deep; it is a mutual induction over `infer`
/// that has not been written.
assume val specialize_typed (env:wenv) (d:dict) (t:term { well_typed env t })
  : Lemma (requires dict_agrees env d)
          (ensures  well_typed env (specialize env d t))

(* ------------------------------------------------------------------------ *)
(* Word rebinding: specialization in its first useful form                  *)
(* ------------------------------------------------------------------------ *)

/// `M05.subst_words` IS `specialize` RESTRICTED TO ONE KIND OF STATIC EFFECT,
/// and it is the first piece of D-02 that actually runs.
///
/// Resolving a word against a dictionary frame is a static effect being
/// discharged (D-37): the surface `with { old new } { body }` installs a
/// Dictionary handler, the elaborator discharges it immediately, and the
/// residual program is that substitution. Nothing about the rebinding survives
/// into the term, which is exactly what E3 below says a fully static effect
/// must cost -- demonstrated rather than assumed.
///
/// It lives in M05 rather than here because it needs no environment: it is a
/// rewrite of syntax, not a use of the typing judgment. That also keeps it
/// inside the modules P03 extracts, which the general `specialize` is not.
///
/// The general `specialize` will subsume it by inlining the replacement as
/// well; keeping it separate now means the substitution is DEFINED and runs,
/// where `specialize` is still `assume val`. E7 below states what it preserves.

(* ------------------------------------------------------------------------ *)
(* The reflective tower                                                     *)
(* ------------------------------------------------------------------------ *)

/// Which compiler stages a program's dependency tree actually requires.
///
/// The key property, and the reason D04 calls binary cost opt-in: this is
/// computed from the EFFECT ROW, using machinery that already exists for
/// typing. A program that never mentions `TSpecialize` and declares no
/// compile-adjacent effect needs no stage at all, so nothing is embedded. A
/// program that JITs needs the specializer and the backend, and gets exactly
/// those.
type stage_req =
  | ReqNone      : stage_req   // no compiler in the binary
  | ReqSpecial   : stage_req   // specializer only: staged code, no codegen
  | ReqCodegen   : stage_req   // specializer plus backend: true JIT
  | ReqFull      : stage_req   // parser through backend: eval, metacompiler

/// Compute the requirement from a term.
///
/// TWO OF THE FOUR ANSWERS ARE CURRENTLY UNREACHABLE, and saying so is more
/// useful than an `assume val` that pretends otherwise. `ReqNone` and
/// `ReqSpecial` are decided by `M05.needs_compiler`: a `TSpecialize` surviving
/// into the term is by definition one the elaborator did not discharge, so the
/// specializer must be present at runtime, and a term without one needs no
/// compiler stage at all. That is the whole of E5, and it is the answer the
/// linker actually consumes.
///
/// `ReqCodegen` and `ReqFull` cannot be distinguished yet because nothing in
/// `M05.term` can demand them. `ReqCodegen` means the residual must be EMITTED
/// as machine code rather than interpreted, and the core has no way to say
/// that -- `TSpecialize` produces a term, and whether that term is then run by
/// an interpreter or by a backend is a property of the host, not of the
/// program. `ReqFull` additionally needs a term that consumes source text, and
/// there is no `eval`. Both become reachable when D04's staging annotations
/// reach the core; until then, returning them would be a guess.
///
/// `env` is unused and kept deliberately: the fine-grained version reads the
/// effect row, which needs it, and changing the signature later would ripple
/// through E5.
let stage_required (env:wenv) (t:term { well_typed env t }) : Tot stage_req =
  if needs_compiler t then ReqSpecial else ReqNone

/// The half of E5 that is available today: a term mentioning no `TSpecialize`
/// requires no compiler stage. Immediate from the definition, and recorded as a
/// lemma rather than left implicit because it is the property a linker would
/// rely on to omit the specializer entirely.
let lemma_no_specialize_needs_nothing (env:wenv) (t:term { well_typed env t })
  : Lemma (requires not (needs_compiler t))
          (ensures  stage_required env t == ReqNone) = ()

(* ------------------------------------------------------------------------ *)
(* The staging obligations, as types                                        *)
(* ------------------------------------------------------------------------ *)

/// E1 and E3 are STATABLE and stated (D-64, D-69); E2 is not yet, and the
/// difference says exactly what is missing.
///
/// A type here is checked but not assumed, so writing one costs nothing and
/// catches a statement that mentions the wrong thing. What it cannot do is make
/// `specialize` exist: both types below are inhabited only by a proof about a
/// function that is still `assume val`, so they are uninhabited for a reason
/// that is not a proof difficulty.

/// E1. Specialization changes a program's cost, never its interface.
///
/// `dict_agrees` is the hypothesis D-69 said was missing and D-74 could finally
/// write: without it `d` may bind a word to a body of some other signature, and
/// the residual is a different program rather than a cheaper one. It is NOT a
/// deficiency of `specialize` that the hypothesis is needed — it is what makes
/// the dictionary a dictionary.
let e1_type : Type =
    (env:wenv) -> (d:dict) -> (t:term { well_typed env t })
  -> Lemma (requires dict_agrees env d)
           (ensures  well_typed env (specialize env d t) /\
                     fst (Some?.v (infer env (specialize env d t)))
                     == fst (Some?.v (infer env t)))

/// E3. A fully static, fully resolved row leaves nothing behind.
///
/// NOTE WHAT THIS DOES AND DOES NOT SAY, because D04 §4 overstates it and the
/// gap has widened. `M06.is_pure` is `Nil? row` — a statement about the ROW,
/// not about the residual term. A `THandle` whose effect is discharged is
/// already `is_pure` while its denotation is full of `M04.Op` nodes, so E3 does
/// not say "the residual contains no effect operations at all".
///
/// That was true before and is now universal: since D-68 every `if` elaborates
/// to a handler around a dispatch, so EVERY conditional is a discharged handler
/// with live `Op` nodes underneath. E3 as stated is satisfied by such a program
/// without erasing anything.
///
/// The zero-cost claim therefore needs a second statement E3 does not make —
/// that the residual contains no handler frame for a static effect either — and
/// that one is FALSE for a case on a runtime tag, which can never be folded.
/// The honest resolution is that `THandle e [] TNil impls (TDispatch ops vs)`
/// is a syntactically recognisable shape (it is exactly what `E05.locate`
/// matches) which a backend compiles to a branch. That is a compiler pass, not
/// a theorem about `specialize`, and D04 §4 should say so.
/// THREE HYPOTHESES NOW, and each earns its place against the definition D-74
/// gave `specialize`. `dict_agrees` is E1's, since a residual that is not well
/// typed has no row to be empty. `dict_ordered` is the completeness condition:
/// the pass descends once through the id space, so a body that calls a word
/// already passed keeps its call, and a disordered dictionary leaves static
/// effects behind without diverging. `resolvable` is the original — `d` has to
/// carry the effects at all.
let e3_type : Type =
    (env:wenv) -> (d:dict) -> (t:term { well_typed env t })
  -> Lemma (requires all_static (snd (Some?.v (infer env t))) /\
                     resolvable d (snd (Some?.v (infer env t))) /\
                     dict_agrees env d /\ dict_ordered d)
           (ensures  is_pure env (specialize env d t))

(* ------------------------------------------------------------------------ *)
(* Obligations                                                              *)
(* ------------------------------------------------------------------------ *)

/// E1  RESIDUAL TYPING.
///     `well_typed env (specialize env d t)`, and its inferred signature is
///     the signature of `t`. Specialization changes the program's cost, never
///     its interface.
///
/// E2  SEMANTIC PRESERVATION -- THE ZERO-COST THEOREM.
///     For `t` well typed with row `row`, and `d` resolving every static
///     effect of `row`:
///
///         denote_static env (specialize env d t)  ==  handle_d (denote_static env t)
///
///     where `handle_d` is `M04.handle` at the handlers `d` supplies for the
///     static effects. In words: specializing is the same as running with the
///     dictionary installed. Everything else in this module is a corollary.
///
///     `handle_d` is not a new construct and must not become one. It is a fold of
///     `M04.handle` over `d.frames`, which is exactly what the ambient Dictionary
///     means (M10) -- and since a word call is already an `Op` node (D-60), the
///     statement covers word resolution and effect handling with one equation
///     instead of two.
///
///     Note the domain: `specialize` must land in `denote_static`'s fragment for
///     the left side to typecheck, i.e. it must discharge every `TSpecialize` it
///     is given. That is a genuine constraint on the definition rather than an
///     artefact of the statement -- a specializer that emitted a residual
///     `TSpecialize` would be deferring work it was asked to do, and D04's
///     two-tier design says a `SDynamic` effect defers by staying an OPERATION,
///     not by leaving a staging node behind.
///
/// E3  STATIC EFFECTS ARE ERASED.
///     If `all_static row` and `d` resolves it, then `is_pure env (specialize
///     env d t)`. The residual program has NO effect operations at all, so
///     nothing about the abstraction survives into the emitted code.
///
///     This is the precise form of "compile-time specializations cost nothing
///     at runtime". It is what licenses building the object model, the module
///     system, generics and interface dispatch all on the effect machinery
///     without paying for any of them -- and it is the theorem to reach for
///     whenever someone suspects the unification of D03 is too clever to be
///     fast. M06's `lemma_static_specializes_to_pure` is the type-level half
///     and is already proved.
///
/// E4  JIT CORRECTNESS.
///     E2 with `d` constructed at runtime. No separate theorem is required,
///     and that is the entire point: the JIT is correct because
///     specialization is correct, so there is no second trusted path from
///     source to machine code.
///
/// E5  STAGE MINIMALITY.
///     If `stage_required env t = ReqNone` then no compiler stage is
///     reachable from `t`, so a linker may omit all of them. The theorem that
///     makes the reflective tower's binary cost genuinely opt-in rather than
///     merely usually-small.
///
///     The SYNTACTIC half is `lemma_no_specialize_needs_nothing` above and is
///     trivial. The content is the other direction of the implication -- that
///     `needs_compiler t = false` really does mean no reachable code path
///     enters the specializer -- which is a statement about `denote` and the
///     word environment, not about `t` alone: a word `t` calls could itself
///     specialize. Discharging it needs the reachability closure over
///     `env.w_effs`, which the specification does not yet have.
///
/// E7  REBINDING PRESERVES SIGNATURES.
///     If every pair `(w, w')` in `su` satisfies `w_sig env w == w_sig env w'`,
///     then for every `t`,
///
///         fst_of (infer env (subst_words su t))  ==  fst_of (infer env t)
///
///     and in particular `well_typed env t ==> well_typed env (subst_words su t)`.
///     The effect ROW may legitimately differ: a replacement is allowed to
///     perform effects the original did not, which is the whole reason to
///     rebind a word.
///
///     STATED IN PROSE RATHER THAN AS A LEMMA, because a stub proving nothing
///     would be worse than an honest gap. Discharging it is a mutual induction
///     over `infer` / `infer_branches` / `infer_impls`: every case but `TWord`
///     is structural and immediate, `TWord` is the hypothesis, and `THandle`
///     needs additionally that `op_of env.w_ops` is unchanged -- which holds
///     because `subst_words_impls` deliberately does not substitute the key.
///
///     `E04_Elaborate` currently enforces the hypothesis by CHECKING, at the
///     point a `with` is elaborated, that the two words have equal signatures.
///     That check is what makes the unproved theorem safe to rely on today; it
///     becomes redundant, not wrong, once E7 is discharged.
///
/// E6  TOWER COLLAPSE.
///     Specializing an interpreter for catcat, written in catcat, against a
///     fixed program yields a residual equivalent to specializing that
///     program directly -- the first Futamura projection. Not needed for the
///     language to work, but it is the theorem that makes the metacompiler
///     goal of D01 precise, and it is the natural place to check that the
///     staging design is strong enough before committing to self-hosting.
