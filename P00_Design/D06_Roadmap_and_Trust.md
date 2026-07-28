# D06 — Roadmap, Phases, and the Trust Story

---

## 1. Phase structure

Directories are numbered so that dependency order and reading order coincide.
`P00`/`P01` exist; the rest are named here and not yet created.

| Phase | Contents | Status |
|---|---|---|
| `P00_Design/` | These documents. | **exists** |
| `P01_Specification/` | Mechanized core: M01–M11. | **exists**, M01–M06 complete |
| `P02_Reference/` | Reference interpreter extracted from F*. | **exists and runs**, R01–R06 |
| `P03_Elaboration/` | Lexer, parser, name resolution, elaboration to core, REPL. | **exists, REPL runs**, E01–E05 |
| `P04_Compiler/` | IR and optimization passes. | planned |
| `P05_Backend/` | Cranelift/LLVM code generation. | planned |
| `P06_Tooling/` | Language server, debugger, profiler. | planned |

`P01_Specification-old/` is the abandoned first attempt, retained until its
replacement is judged adequate. Nothing in it is salvaged — D01 §3.4 records why.

---

## 2. Bootstrapping: F* as the source of truth

The compiler is written in catcat, but it is **not hand-written** in catcat.

- Compiler passes are F* functions over `M05_Terms.term`, proved correct against
  the M07 semantics.
- They **extract to OCaml** for stage 0 — the same pipeline the repository
  already uses for `fstar/Catcat.Core.fst`.
- A verified printer emits the same passes as **catcat source** for self-hosting.

So self-hosting is a *consequence of extraction*, not a second implementation.
There is one artifact and one proof, which is what keeps the verification story
tractable. This is also why `term` is a core specification type rather than a
compiler-internal detail (M05's header notes this).

### Extraction target: OCaml, not Pulse/C/Rust

**Decision: the bootstrap compiler extracts F* to OCaml. Pulse is not used.**

The reasoning, since it is the kind of choice that gets revisited:

- A compiler middle-end is a **pure tree-to-tree transformation** — ASTs in,
  ASTs out. Pulse exists to verify imperative, pointer-manipulating code with
  separation logic. That is not the shape of this problem, so the tool's central
  capability goes unused.
- The passes are already F* functions over `M05_Terms.term` and extract to OCaml
  essentially for free; the repository already does this for
  `fstar/Catcat.Core.fst`.
- Pulse would add a second proof discipline, Karamel to the toolchain, a C or
  Rust build, and manual heap management for the AST — all cost, no
  corresponding gain.
- **Bootstrap compiler performance is irrelevant.** It runs once, to build the
  self-hosted compiler. Optimising it is optimising the artifact that gets
  thrown away.
- There is no trust advantage. Karamel and the OCaml extractor are both
  unverified extraction paths; swapping one for the other moves the trust
  boundary without shrinking it.

OCaml's role stays what it is today: thin glue that disappears once self-hosting
lands.

**Where Pulse should be revisited — P05 and the runtime.** The allocator,
concurrency primitives, and above all the JIT's code buffers (`mmap`, W^X page
management, i-cache coherence) are genuinely imperative memory work where
separation logic pays for itself. That is a real candidate later; the compiler
is not.

### The bootstrap trust problem

A self-hosted compiler that compiles itself does not have its *binary* verified
by verifying its *source* — Thompson's "Reflections on Trusting Trust". The
mitigations, in order of cost:

1. **Trusted stage 0 from F*.** The OCaml-extracted compiler is the root of
   trust; its provenance is F* extraction, not a previous catcat binary.
2. **Diverse double-compiling** (Wheeler). Build the self-hosted compiler with
   two independent stage-0 paths and compare the fixed points.
3. **Reproducible builds** throughout, so any divergence is detectable.

This must be settled *before* self-hosting, not after. E6 (tower collapse, D04
§6) is the natural checkpoint: if the staging design cannot express a catcat
interpreter in catcat and collapse it, self-hosting is premature.

---

## 3. Trust tiers

Each tier ships value alone. The project is never blocked on completing the next.

### T1 — Mechanized specification *(current)*

Syntax, types, semantics, soundness. Delivers: a design that is precise enough to
disagree with, and a soundness argument for the type system.

Done: M01–M06 verified. Remaining: `M03.lemma_compose_assoc`, then `M07.denote`,
then M07's T2–T6, then M08–M11.

### T2 — Reference interpreter

Extracted from F*, proved to agree with the denotational semantics (M09, S5).
Delivers: an executable spec, and the oracle every later tier tests against.

**S5 is the single most valuable theorem in the project.** Without it the
denotational semantics and the running artifact are unrelated, and every
compiler-correctness claim afterwards is stated relative to nothing.

### T3 — Verified compiler passes

Each IR pass verified against T1 semantics, one at a time. Unverified passes fall
back to differential fuzzing against T2. Delivers: incremental confidence, with
no all-or-nothing cliff.

The draft's requirement that each optimization provably match the original
behaviour "according to spec rules which consider the full application as an
unstructured DAG of computations" is exactly what M07's T2 (sequencing = Kleisli
composition) licenses: it is what makes the DAG view sound.

### T4 — Backend

Unverified. Cranelift or LLVM, with translation validation at the boundary.

The draft's concern about Cranelift is correct and worth restating: an
unverifiable backend that exploits aliasing assumptions the source language does
not guarantee is a real soundness gap, not a theoretical one. Two responses:
keep the IR handed to the backend conservative about aliasing, and put
translation validation — not proof — at the T3/T4 seam.

---

## 4. Calibration

CompCert is roughly a decade of person-effort for a C compiler with **no
effects, no metaprogramming, and no JIT**. catcat has all three.

This is not an argument against the project; it is an argument for the tiering.
The realistic reading is that T1 and T2 are achievable, T3 is achievable pass by
pass and indefinitely extensible, and T4 will not be verified. Any plan that
requires T4 to be verified before the language is usable is a plan that does not
finish.

---

## 5. Immediate next steps

Two tracks, run in parallel rather than in series. Discharging admits and
getting a running interpreter are equally important, and sequencing them
strictly would mean either a spec nobody can execute or an interpreter nobody
can trust.

### Track A — a running system

The priority is to have something that executes catcat, then something that
compiles it, both adhering to the spec.

**Done:** P02 runs — R01–R06 verify, extract to OCaml, and evaluate arithmetic,
sealed classes, sums, and handled and unhandled effects. **Recursive types are
in the core** (D-25) — see below. **P03 runs**: `make catcat` gives a REPL that
takes a line of surface catcat through lex → parse → elaborate → M06 typecheck
→ evaluate. See "The surface language, prototyped" below.

1. **Meta-interpreter**: the catcat interpreter written in catcat, run on the
   extracted one. First real test of the staging design, and the checkpoint for
   E6 (tower collapse). Blocked on N02 Q-10 — `wenv` and `sig_env` have
   function-typed fields, so any pass constructing one cannot extract to catcat.
2. **Extend P03 to the rest of D05**, in rough order of value: effect rows and
   handler syntax (exercises D03's unification), sums and classes, `let`,
   modules and `::`, generics, then macros.
3. **Compiler and extractable meta-compiler (P04)**, with the stack-to-SSA pass
   of D04 §7 as the first priority — before any backend work, since nothing
   downstream performs without it.

#### The surface language, prototyped

The prediction in the previous revision of this list — that D05 design errors
would be "far cheaper to find here than after codegen exists" — held. Building
the elaborator found two:

- **`dup`/`pop`/`swap` cannot express locals.** They reach only the top two
  slots, and no composition of them touches a third, so `$x` was
  unimplementable. The core gained `pick`/`roll` (D-29, D02 §7). Design review
  had not caught this; the first attempt to compile `$x` did, immediately.
- **`--` was not self-delimiting**, so `( i64--i64 )` lexed as one word while
  `{$x $x mul}` worked (D-28).

Implemented: literals, words, `define` with signatures, named parameters with
the suffix rule, the shuffles instantiated from the compile-time shape,
`Box[]`/`Rc[]`, `\` comments. Not yet: macros, modules, generics, effects and
handlers, sums and classes, strings, `let`.

#### Recursive types: done

Attempting the catcat encoding of the interpreter's own data types found that
**`M01_Kinds.dtype` could not express recursion.** Every case was structural
and finite; `TSeal` carried its representation inline rather than referring to
a declaration. So `list` — the type the entire interpreter is built from — was
not expressible, and neither were `rvalue`, `term`, or `kont`.

**The fix (D-25):** `dtype` gained `TName nom_id` — an explicit forward
reference to a declaration — plus pointer types `TBox`/`TRc` (owning and
shared, Rust-named). Recursion is legal only *through a pointer*:
`List = TSum [[]; [TPrim PI64; TBox (TName list_id)]]`. `dtype` values stay
finite trees because `TName` is a leaf, so there is no positivity obligation;
and no environment was needed in M01/M02 because a pointer's capabilities
don't depend on its pointee, so `has_cap` never has to resolve a `TName`. M01's
`wf` rejects a bare `TName` not behind a pointer. Full account:
[R06_SelfHost](../P02_Reference/R06_SelfHost.fst) §3.

**Sequencing still matters.** P04's IR must not be written against the old,
non-recursive `dtype` — it targets M01 as it now stands. Had `dtype` changed
after P04 started, the IR would have needed rewriting; this is why the fix
went in first.

### Track B — closing the proof gaps

4. **Discharge `M03.lemma_compose_assoc`.** Four-way case analysis on which
   segment runs out; closes by `append_assoc` and `lemma_unify_disjoint`.
   Needed before `denote` because it is the same transport reasoning.
5. **Restate `M04.free` over `FStar.FunctionalExtensionality.(^->)`** and
   discharge `lemma_fbind_right_id` and `lemma_fbind_assoc`. Mechanical but
   invasive; doing it early avoids redoing the M07 inductions.
6. **Define `M07.denote`** and prove **T2** (sequencing = Kleisli composition),
   the central theorem.
7. **Prove S5** (agreement between M07 and M08), retroactively justifying the
   interpreter built in step 2.

### Crossing between tracks

8. **Build the erasure harness** (D04 §7) as soon as P02 exists. The zero-cost
    claim needs an empirical check alongside E3; discovering late that residuals
    are bloated would be expensive, and the harness is what turns "the optimizer
    must be competent" into a measurable bar.

---

## 6. Open questions

Recorded rather than resolved, and none of them block the next steps.

- **Deep-handler typing.** M06's `THandle` rule checks implementations against
  the operation's declared signature, which is correct for interface/class
  methods and for handlers that resume exactly once. Handlers that capture and
  reuse the continuation explicitly need the continuation in their signature.
  Deferred to M10.
- **Dependent types.** Correctly lowest-priority in the draft. Nothing in the
  design forecloses them; `TSeal` carrying its representation would need to
  become environment-relative first.
- **Concurrency.** Listed as a built-in effect (D03 §7) but not specified.
  Effect handlers are a natural fit; the interaction between linear types and
  concurrent ownership is the part that needs real thought.
- **`'…'` quotation.** Reserved, recommended, uncommitted (D05 §6).
- **Numeric tower.** M01 uses mathematical bounded integers and abstract floats.
  Wrapping, saturation and IEEE-754 semantics are properties of *operations*,
  and belong in a module M01 does not yet have.
- **The coercion table.** D04 §3.1 fixes the rules but not the contents. The
  set should be decided once, checked for confluence offline, and kept small
  enough to print on one page — the rules keep inference fast at any table size,
  but readability does not.
