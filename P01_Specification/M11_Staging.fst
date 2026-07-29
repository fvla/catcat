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
/// STATUS: skeleton. Types and the reflective-tower interface are real;
/// `specialize` is declared, not defined.

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

/// Resolve every statically-staged effect of `t` against `d`, producing a
/// residual program.
///
/// NOT DEFINED. The definition is a partial evaluator over `M05.term`:
/// inline statically resolved words, fold `TCase` on known tags, erase
/// `TPack`/`TUnpack` (sound by M10's H4), and leave dynamic operations alone.
/// It is the single largest piece of unwritten work in the specification and
/// should not be attempted before M07's `denote` exists, since E2 is stated
/// against it.
assume val specialize (env:wenv) (d:dict env.w_ops) (t:term { well_typed env t })
  : Tot term

/// The residual is still well typed, with the static effects gone. Stated
/// separately from E2 because the compiler needs it long before anyone proves
/// semantic preservation, and because M06's `lemma_static_specializes_to_pure`
/// already establishes the type-level half.
assume val specialize_typed (env:wenv) (d:dict env.w_ops) (t:term { well_typed env t })
  : Lemma (well_typed env (specialize env d t))

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

/// Compute the requirement from a term. Uses `M05.needs_compiler` for the
/// coarse question and the effect row for the fine one.
assume val stage_required (env:wenv) (t:term { well_typed env t }) : Tot stage_req

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
///         denote env (specialize env d t)  ==  handle_d (denote env t)
///
///     where `handle_d` applies the handlers `d` supplies for the static
///     effects. In words: specializing is the same as running with the
///     dictionary installed. Everything else in this module is a corollary.
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
