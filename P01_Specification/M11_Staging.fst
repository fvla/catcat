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

/// The pass is `M05.resolve_defs` (D-76), which needs neither a `dict` nor the
/// typing judgment — a table of bodies is an association list. This wrapper is
/// what makes it a DICTIONARY operation, and the move is what lets `E04`
/// discharge a static Dictionary frame without the denotation in its dependency
/// set. The argument for why one descending pass suffices is at `resolve_defs`.
let resolve_below (d:dict) (n:nat) (t:term) : Tot term =
  resolve_defs d.d_defs n t

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
///     THE ELABORATOR ALREADY DOES IT (D-83). `E06.discharge_dict` discharges
///     the node the same way — `resolve_defs` over its body — because that is
///     where every generic instance arrives, and it can: at elaboration time the
///     residual is handed straight to `M06.infer`, so E1's question is answered
///     by running the checker rather than by a proof. The two agree on what
///     discharging MEANS; what E1 buys is the right to do it without checking.
///
/// The `well_typed` refinement is not consumed. It is kept because E1, E2 and E3
/// are all stated at it and a signature change here would ripple through three
/// obligation types for no gain.
let specialize (env:wenv) (d:dict) (t:term { well_typed env t }) : Tot term =
  resolve_below d (word_bound t) t

/// A dictionary with nothing in it changes nothing. The sanity check that the
/// pass is doing lookup rather than rewriting, and the one property of
/// `resolve_below` that needs no ordering hypothesis.
let rec lemma_resolve_defs_empty (n:nat) (t:term)
  : Lemma (ensures resolve_defs [] n t == t) (decreases n) =
  if n = 0 then () else lemma_resolve_defs_empty (n - 1) t

let lemma_specialize_empty (env:wenv) (t:term { well_typed env t })
  : Lemma (specialize env empty_dict t == t) =
  lemma_resolve_defs_empty (word_bound t) t

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
/// does not rewrite an implementation's key. Nothing here is deep; it is a
/// mutual induction over `infer` that has not been written.
assume val specialize_typed (env:wenv) (d:dict) (t:term { well_typed env t })
  : Lemma (requires dict_agrees env d)
          (ensures  well_typed env (specialize env d t))

(* ------------------------------------------------------------------------ *)
(* Word rebinding: specialization in its first useful form                  *)
(* ------------------------------------------------------------------------ *)

/// `with` IS `specialize` RESTRICTED TO ONE EFFECT, and it is the first piece
/// of D-02 that actually runs. `E04` elaborates `with { old new } { body }` to
/// `THandle eff_dict [] TNil [(old, TWord new)] body`, and `E06.discharge`
/// resolves that frame away with the SAME `M05.resolve_defs` this module's
/// `specialize` calls. One function, two call sites, which is the claim.
///
/// THIS SECTION USED TO SAY `M05.subst_words` WAS THAT RESTRICTION, AND IT WAS
/// WRONG (D-76). A rename rewrites the calls the block itself writes; handling
/// the Dictionary effect reaches a call the block makes INDIRECTLY, because the
/// frame stays installed while the callee runs. D-75 produced the
/// counterexample the moment the runtime path existed:
///
///     with { greet bye } { shout }                        -- gave "hello!"
///     handle Dict … { greet { bye } } { shout }           -- gave "goodbye!"
///
/// Two spellings of one construct disagreeing on a result is exactly what D-02
/// says cannot happen, so the substitution is gone and `with` is the handler.
/// Both now give "goodbye!", and `locate` shows the residual — `bye "!" cat`,
/// with `shout` inlined and nothing of the rebinding left.
///
/// The claim was not merely unproved; it was false, and it survived because
/// nothing could compare the two until the dynamic side ran.

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
///
/// THE EQUALITY IN THE CONCLUSION IS TOO STRONG SINCE D-84, and the eventual
/// proof will have to weaken it. A declared signature may now FRAME the body's
/// inferred one, so `infer` of `TWord w` reads a signature the stored body only
/// satisfies up to a residual `k`. Inlining therefore replaces a term by one
/// with a MORE GENERAL signature, and `==` should be "frames to" —
/// `M06.impl_frame` at the empty state segment, exactly as `E06.sig_frames` uses
/// it. Soundness is unaffected, since `compose` frames; the statement is what is
/// wrong, and stating it wrongly here would be worse than saying so.
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
/// E7  REBINDING PRESERVES SIGNATURES -- WITHDRAWN (D-76), because the
///     function it was about is gone.
///
///     It said: if every pair in `su` has `w_sig env w == w_sig env w'`, then
///     `subst_words su` preserves inferred signatures. `subst_words` was
///     deleted when `with` became a Dictionary handler, and nothing renames a
///     word any more.
///
///     Both halves are now someone else's. The hypothesis is `M10.dict_agrees`
///     and the conclusion is E1, which says exactly this about `specialize` and
///     therefore about `with` — including that the effect ROW may legitimately
///     differ, since a replacement performing effects the original did not is
///     the whole reason to install one. And the CHECK `E04` used to make, an
///     equality test standing in for the unproved theorem, is now
///     `M06.infer_impls` typing the replacement at the operation's declared
///     signature: the ordinary handler rule, weaker than equality in the way
///     `impl_frame` is (D-68), and kept in `E04` only to locate the mistake in
///     a message.
///
/// E6  TOWER COLLAPSE.
///     Specializing an interpreter for catcat, written in catcat, against a
///     fixed program yields a residual equivalent to specializing that
///     program directly -- the first Futamura projection. Not needed for the
///     language to work, but it is the theorem that makes the metacompiler
///     goal of D01 precise, and it is the natural place to check that the
///     staging design is strong enough before committing to self-hosting.
