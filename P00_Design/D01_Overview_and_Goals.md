# D01 — Overview and Goals

**catcat**: con*cat*enative, *cat*egorical. A statically stack-typed concatenative
language with algebraic effects, staged compilation, and a mechanized core.

This document states what the language is for, which goals are achievable and
on what evidence, and how the pieces are layered. D02–D05 specify the design;
D06 gives the build order and the trust story.

---

## 1. The two ideas the design rests on

Everything else in this specification follows from two observations. Both are
implicit in the original draft; naming them is what turns a list of ambitions
into a design.

### 1.1 Effects, interfaces, traits, classes, modules and the Dictionary are one construct

An **interface** is a set of word declarations with stack signatures. A
**handler** supplies implementations for them. That is the entire mechanism, and
it plays every one of these roles:

| Role | Interface is… | Handler is… |
|---|---|---|
| Algebraic effect | the operation signature | the `handle` block |
| Typeclass / trait | the class declaration | the instance |
| Class / object | the method table declaration | the class body |
| Module | the module's exported signature | the module implementation |
| The Dictionary | the ambient word namespace | a scope that rebinds words |

These are not analogies. In [M10_Handlers.fst](../P01_Specification/M10_Handlers.fst)
there is one `handler` record type, and all six uses are the same value. Typeclass
dictionary-passing and effect-handler-passing become literally the same
mechanism — the pun in "dictionary" is load-bearing.

The consequence for the language user is that there is one thing to learn, and
one set of rules for how it scopes and resolves. The consequence for the
implementation is that there is one thing to optimize, so making interface
dispatch free (§1.2) makes *all six* free at once.

### 1.2 Compile-time specialization and runtime JIT are the same operation

`specialize(program, dictionary)` resolves a program's statically-staged effects
against a dictionary and emits a residual program.

- Run it at **elaboration time** and it is monomorphization, inlining, and
  interface resolution. Because the resolved effects are *erased*, the
  abstraction costs nothing at runtime.
- Run it at **runtime**, with a dictionary the running program constructs, and
  it is the **JIT**.

Same function, same correctness theorem
([M11_Staging.fst](../P01_Specification/M11_Staging.fst), E2), two call sites.
The draft's formulation — "a JIT function is a function with user-defined
effects instantiated at runtime" — is correct, and this is its precise form.

This is why manual JIT is not a separate subsystem bolted onto a compiler, and
why there is no second trusted path from source to machine code.

---

## 2. Feasibility, goal by goal

The honest summary is: **feasible as layers, not as one thing.** Each layer below
is independently useful, and the ordering is forced by dependency. D06 turns this
into a schedule.

| Goal (from the draft) | Verdict | Notes |
|---|---|---|
| Concatenative core, statically stack-typed | **Solved problem** | Row-polymorphic stack typing is well-trodden: Kitten, Factor, Diggins' Cat, Joy. The typing judgment is one page ([M06](../P01_Specification/M06_Typing.fst)). |
| Algebraic effects with handlers | **Solved problem** | Koka, Eff, Frank, OCaml 5. Deep handlers give the draft's "every effect is reentrant" for free. |
| Effects unified with interfaces/classes/modules | **Novel, low risk** | The combination is new but each half is standard. Stack rows and effect rows are the same machinery — Koka already does this for effects alone. |
| Staged specialization, zero runtime cost | **Achievable, real prior art** | Terra, LMS, MetaOCaml. The zero-cost claim is stated as a theorem (E3), not assumed. |
| Manual JIT | **Achievable** | Falls out of §1.2. The risk is design drift, not feasibility. |
| Metacompiler / reflective tower | **Achievable, hardest layer** | See "Collapsing Towers of Interpreters" (Amin & Rompf, POPL 2018) — closest existing formal treatment. |
| Linear types from the stack | **Achievable, but not free** | See §3.3 — it is opt-in capabilities, not an automatic consequence. |
| Fast incremental LSP | **Achievable** | Type inference *is* signature composition, so re-checking a token means recomposing one spine. §3.5. |
| C/Rust-competitive speed | **Plausible, unproven** | Depends entirely on erasure (E3) holding in the real compiler. The design makes it checkable; nothing here makes it automatic. |
| Verified compiler end to end | **Not achievable as stated** | See §4. Tiered trust instead. |
| Dependent types in the core | **Deferred** | Correctly lowest priority in the draft. Nothing here forecloses it. |

### 2.1 Prior art worth reading before the next design pass

- **"Collapsing Towers of Interpreters"** (Amin & Rompf, POPL 2018) — a tower of
  interpreters staged so the levels collapse away. This is the closest existing
  treatment of the embedded-compiler idea and should be read before D04 is
  finalized.
- **Terra** (DeVito et al.) — Lua staging a low-level compiled language, JIT via
  LLVM. The closest working system to the metacompiler vision.
- **LMS**, Lightweight Modular Staging (Rompf & Odersky) — the type-directed
  staging discipline.
- **Kitten** and **Factor** — row-polymorphic stack typing in practice; Kitten
  for the type system, Factor for what quotations-always-inlined feels like at
  scale.
- **Koka** (Leijen) — effect rows and their inference, essentially the effect
  half of this design already built.
- **CompCert** — for calibration on §4.

---

## 3. Corrections to the draft

Five positions in the original draft do not survive contact with the rest of the
design. Each is corrected below and specified in the referenced document.

### 3.1 Sums must be primitive (D02 §4)

Products genuinely do fall out of stack segments plus nominal sealing — that part
of the draft holds, and a "tuple" in catcat is just a run of stack slots.

Sums do not. A stack's shape is static; a sum has a *different shape per branch*.
No amount of erasure produces that. They are also needed for `option`/`result`,
and handler dispatch needs them anyway. So: tagged unions are primitive, with a
tag plus max-variant layout.

### 3.2 Code is first-class; functions are not (D02 §6)

"No first-class functions" as literally stated conflicts with `{}` blocks, effect
handlers, `if`/`while`, and the JIT — all of which are code values.

The resolution matches the draft's actual intent: **a `{}` block is either
executed directly or consumed by a macro.** So code is first-class *at
elaboration time*, and there are no runtime closure values. A quotation never
reaches the value stack; it appears only as a syntactic argument to a construct
that consumes it. Every block is therefore inlinable, and no heap-allocated
environment exists.

### 3.3 Linearity is opt-in, not automatic (D03 §5)

The stack gives *affine slot use* — a value is consumed when popped. But `dup`
breaks linearity and `drop` breaks relevance, so linearity is not an automatic
consequence of stack semantics.

Instead, types carry `Copy`/`Drop` capabilities exactly as in Rust: `dup`
requires `Copy`, `pop` requires `Drop`, and `Clone` is an ordinary interface. A
type with neither is linear. This is what makes `delete` in the draft's Counter
sketch mean something — as written there it is a synonym for `pop`, which is a
no-op, not a destructor.

### 3.4 Intrinsic stacks, not refined lists (D02 §2)

The draft's [M01_Syntax.fst](../P01_Specification-old/M01_Syntax.fst) modelled a
stack as `list value` refined by a `splitAt` predicate. This is the direct cause
of the difficulty it ran into:

- Every operation had to re-establish the invariant by hand, so the module
  accumulated lemmas about `splitAt` and none about the language.
- The frame property was stated as a refinement *on each function*, making it a
  proof obligation at every definition site instead of a theorem proved once.
- `compose_stack_functions` never applied its second argument — the body returns
  `(f stem) @ tail`, so the promised composition was identity with extra steps —
  and its type placed the unification residuals on the wrong sides of the arrow.

Replacing the refined list with an inductive family indexed by `list dtype`
reduces the entire structural burden to **two** lemmas
([M02_Stacks.fst](../P01_Specification/M02_Stacks.fst)), and the frame property
becomes one combinator with one correctness lemma.

### 3.5 Dictionary rebinding must be staged (D04 §2)

If any word's meaning can be rebound by an enclosing handler, a fragment's type
is not determined until the handler chain is known — which would forfeit static
typing, separate compilation, and the fast-LSP goal all at once.

The fix is already present in the draft's Counter sketch: a handler **declares
which words it overrides and with what signatures**. That `interface { declare-word … }`
block is the load-bearing idea. With it, elaboration stays static.

The two-tier design (D04) then keeps the power: a **static** tier resolved at
elaboration and fully erased, plus an explicitly-marked **dynamic** tier that
compiles to handler-frame lookup for the cases that genuinely need it.

---

## 4. What "proof-oriented" can and cannot mean here

CompCert is roughly a decade of person-effort for a C compiler with no effects,
no metaprogramming, and no JIT. Verifying *this* language's whole pipeline to
machine code is not a realistic target, and the draft's own instinct — that
Cranelift cannot be verified and cannot be trusted to respect aliasing
assumptions — is right.

So the trust story is **tiered**, and each tier ships value on its own:

- **T1** — Mechanized spec: syntax, types, semantics, soundness. *In progress;
  this is P01.*
- **T2** — Reference interpreter extracted from F*, proved to agree with the
  denotational semantics (M09 S5). Makes the spec executable.
- **T3** — Compiler IR passes verified against T1 semantics, one pass at a time,
  with differential fuzzing against T2 as the fallback for unverified passes.
- **T4** — Backend unverified, with translation validation at the boundary.

D06 details this. The point is that the project is useful at T1, more useful at
T2, and never blocked on completing T4.

---

## 5. Reading order

Numbered so that dependency order and reading order coincide, in both the design
docs and the mechanization.

| Doc | Contents |
|---|---|
| **D01** | This document. Goals, feasibility, corrections. |
| **D02** | The core calculus: types, stacks, signatures, typing, denotation. |
| **D03** | Effects, interfaces, the object model, linearity. |
| **D04** | Staging, the two-tier Dictionary, JIT, the reflective tower. |
| **D05** | Surface syntax, locals, macros, modules. |
| **D06** | Roadmap, phases, trust tiers, bootstrapping. |

The mechanization in [P01_Specification/](../P01_Specification/) mirrors D02–D04
module by module. `make verify` typechecks all of it; `make admits` lists every
gap. As of this pass, all eleven modules verify and none contains an `admit`; M01–M06
are complete; M07's `denote_static` is defined for the whole core except
`TSpecialize` and `PUnroll`, with T2 discharged by construction, T5 repaired by
D-63, and T3, T4, T6 recorded as obligations; and M08–M11 are skeletons, except
that M10's handler fold is real and lives in M04 (D-59).
