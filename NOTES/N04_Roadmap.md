# N04 — Roadmap: demos, documentation, and the next features

`D06` §5 is the *project* roadmap and stops at "get a running system, close the
proof gaps". This file is narrower and later: it is the plan for the phase that
starts once the surface language runs, which it now does. It exists because the
next three pieces of work — demonstrating utility, documenting what exists, and
choosing which of five large features to build — are not ordered by dependency,
so the order has to be argued rather than derived.

Written 2026-08-16. Sections 1–3 are the plan being executed; §4 is the feature
sequencing, which is a set of recommendations and not decisions.

---

## 0. The question this file answers

> Is the language powerful enough to demonstrate its own thesis?

Yes, and the check was cheap. The thesis (D01 §1) is that **one program can be
re-interpreted two ways**:

- **bottom-up** — a word performs an operation, declares the effect in its
  signature, and the meaning is supplied by whoever handles it further out;
- **top-down** — a caller overrides the handlers of effects a program already
  uses, *including the ambient `!Dict`*, so the words a program calls can be
  redefined underneath it.

Both run today, unmodified, in the REPL:

```
catcat> effect Log { declare say ( str -- ) }
catcat> define work ( i64 -- i64 !Log ) { "w\n" say dup * }
catcat> handle Log over ( i64 ) init { 0 } { say { swap pop 1 + } } { 7 work }
ok  49 1

catcat> define sq ( i64 -- i64 ) { dup * }
catcat> define prog ( i64 -- i64 ) { sq sq }
catcat> handle Dict over ( i64 ) init { 0 } { sq { swap dup * swap 1 + } } { 3 prog }
ok  81 2
```

The second transcript is the whole claim in four lines: `prog` is *unmodified*
code, `sq` is an *ordinary word* and not an operation, and the handler both
reimplements it and counts the calls. That is a profiler written as a handler
over code that knows nothing about profiling.

So the demo work is not blocked on a feature. It is blocked on **infrastructure**
— there is no way to run a file — and that is a half-hour of glue.

## 0a. What is genuinely missing, and what it costs a demo

Checked against the binary, not against `D05`:

| Missing | Blocks a demo of… | Severity |
|---|---|---|
| arrays, lists, any aggregate | anything that processes a collection | **high** — this is the real ceiling |
| substring / split / index on `str` | text processing, a parser, a tokenizer | high |
| surface `Box`/`Rc` construction | a linked structure, ownership | medium |
| `>` and `>=` | nothing — `<` with swapped arguments works | trivial |
| `let`, anonymous loops | readability, not capability | low |
| modules / `::` | naming hygiene in a large demo | low at demo scale |

Everything above the line means the demos must be **control- and
effect-shaped**, not data-shaped. That is an acceptable restriction, because
control and effects are what is novel here; a demo of a list library would
demonstrate nothing this language does differently. It is recorded so that the
demo suite is not mistaken for a claim that the ceiling is elsewhere.

---

## 1. Demo infrastructure

1. **`catcat.exe -f FILE`.** The whole file is fed to `eval_line` as one line.
   This works with no elaborator change because the lexer already treats
   newlines as whitespace and `E06` already parses **one declaration at a time**
   within a line (D-54), so a file is just a long line. Verified: multi-line
   `define`s and `\` comments already survive being passed as a single argument.
2. **`demos/NN_name.cat` + `NN_name.expected`, and `make demos`** which runs
   each and diffs. Golden-output regression, the same discipline `make interp`
   uses, so the demos cannot rot silently.

## 2. The demo suite

Each demo is one claim, and each claim is one the language actually makes.
Ordered so that a reader can start at 01 and stop anywhere.

As built (`demos/README.md` is the index; `make demos` checks all seven):

| # | Demo | The claim it demonstrates |
|---|---|---|
| 01 | tour | it runs: inference, `if`, `recurse`, strings, signatures as assertions |
| 02 | effects, bottom-up | one program, four `Log` handlers: print, discard, count, capture. D-01 |
| 03 | dictionary, top-down | `with` and `handle Dict` reinterpret code that was not written for it — including a profiler over untouched words — and, being one construct at two times, give the same answer with different residuals. D-02 |
| 04 | generics and staging | a generic is `specialize` run early; `locate` shows full monomorphization |
| 05 | mocking C | `extern` + `handle C`: a deterministic test of a program that calls libc |
| 06 | failure | `try`/`catch` as `Fail`'s handler, composing with the rest |
| 07 | three modes | **capstone** — one deploy script run as production, dry run and audit, the third typed as pure |

Staging got folded into 03 and 04 rather than getting a demo of its own: it is
not a separate feature, and giving it one would have implied it was.

## 3. Documentation

Two audiences, two documents, and they are not the same job.

- **`P01_Specification/M00_Reading_Guide.md`** — a way into the mechanized core
  for someone who has not read it. Dependency order, the five types everything
  is built from, where each design claim is *cashed out as a definition*, and an
  honest inventory of what is proved versus stated. This is the file the user
  asked for; it lives next to what it describes rather than in `DOCS/`, because
  `DOCS/` has a charter (the language as it runs) that a spec guide would muddy.
- **`DOCS/U03_Tutorial.md`** — the missing third user document. `U01` is a
  grammar reference and `U02` is a word reference; there is no path *in*. Keyed
  to the demos, so every transcript in it is one `make demos` checks.

Plus: `U01` §4 ends "There is no `while` or recursion yet, so conditionals are
the whole of control flow", which §6 of the same file contradicts. Stale since
`recurse` landed.

---

## 4. The next features, sequenced

Five were named: arrays, references/pointers, memory management, concurrency,
namespaces/modules. They are not independent and they are not equally ready.

**The ordering principle is D-56**: a feature that *removes* core constructors
is worth more than one that adds them, because the core is the thing being
proved about. Two of the five do that; two do not; one is neutral.

### 4.1 First: **surface type declarations.** Everything else is behind them.

*Revised after checking the elaborator rather than the design docs. The first
draft of this section said the library mechanism came first; that was wrong by
one step, and the step is load-bearing.*

The plan was: an F\*-checked library contributes `Box`/`Rc`, the six `prim_op`
rows leave the core (D-56), and an **array** arrives as a library declaration
rather than as a seventh and eighth block of primitives with no proof story.
That is still the destination. What blocks it is not the library mechanism.

**A user cannot declare a type at all.** Checked against the binary:

```
catcat> type Point ( i64 i64 )
error: unexpected ( in a term sequence
catcat> define f ( Point -- ) { }
error: unknown type: Point
```

`E04.elab_ty` resolves `StyName n` against `prim_of_name` and nothing else, so
`TSeal` and `TSum` — the two core constructors that everything aggregate is
built from — are **unreachable from the surface**. The elaborator builds them
internally (`if` compiles to a `TDispatch` over a `TSum`) and no program can
name one. And `Box[T]` is not evidence to the contrary: `E02.sty` has
`StyBox`/`StyRc` as *hardcoded constructors*, not a general application form, so
it is two special cases rather than the beginnings of type application.

So the real order is:

1. **A surface type declaration**, of both shapes the core has: a sum
   (`TSum`) and a sealed record (`TSeal`, which carries its own capability
   list, so this is also where a user-declared *linear* type comes from).
   Needs: `nom_id` allocation in the session, a type table in `nenv`,
   `elab_ty` consulting it, and constructor/eliminator words per declaration.
2. **Type parameters on a declaration.** `sty` gains a general
   `StyApp : string -> list sty -> sty`, which *subsumes* `StyBox`/`StyRc` and
   deletes those two cases. This is the piece Q-18 called "generic NOMINAL
   types"; `TSeal` currently takes `nom_id -> list cap -> list dtype` with no
   parameters, so the core changes here too.
3. **Then** the library mechanism, and then `Box`/`Rc` leave the core.

Steps 1 and 2 pay for themselves several times over before step 3 arrives, which
is why the correction improves the plan rather than lengthening it:

- `bool` becomes a declared two-variant sum, removing `PBoolSum` and
  `prim.PBool`;
- `option[T]` exists, so `parse` and `getenv` stop returning sentinels;
- **D-71's two limits close**: `fail` gets `∀a. ( -- a )` and `catch` a typed
  payload. The core already *has* the empty type — `TSum []` is uninhabited —
  and its eliminator is already spelled, `TDispatch [] []`, which `M06.infer`
  currently rejects on `Nil? variants`. Demo 06's `fail 0` padding goes away;
- a user can write a `case`, which `U01` §5 lists as blocked on exactly this.

**The library mechanism itself stays cheap**, and that part of the first draft
holds. The full `emit : <F* subset> -> term` of `R06` §1 is a metaprogramming
project; the useful 80% is not. A catcat program *is* a value of `M05.term`, so
an F\*-checked library is an F\* module that **produces `term`s and signatures
directly** plus a session pass that installs them — no pretty-printer, no parser
round-trip, no reflection on F\* syntax. `R06` §1's own argument for why the AST
is the artifact applies at this scale too.

One thing to settle when step 3 arrives: a `gentry` stores `g_body : list
sterm`, i.e. **surface** AST, and `install_instance` re-elaborates it per
instantiation. A library generic emitting core `term`s directly does not fit
that path. Either generics gain a second, already-elaborated body form, or a
library ships surface source — which `-f` now makes viable and which is worth
pricing before assuming the F\* route.

So: **arrays and memory management are downstream of type declarations, and
type declarations are the single highest-value thing left.** They are also the
only item on the list that is pure addition — no decision in `N01` has to be
revisited to build them.

### 4.2 Second: namespaces/modules — cheap, and already designed

D-10 says modules are Dictionary handlers, and `handle Dict` exists (D-75/D-76).
A `module M { … }` is a set of definitions plus a naming convention, and `use M`
is a static `Dict` frame — which is `with` under a different spelling. The
lexing is LL(1)-safe because `M::f` is one word to a DFA (word names are already
free-form, D-32), so **nothing about D-30 is at risk**.

The reason it is second rather than first is that it buys hygiene, not power,
and the demos are small enough not to need it. The reason it is not last is that
it gets much more expensive after the library mechanism ships with a flat
namespace.

### 4.2a A note on where the demos hit the ceiling

Worth recording because it agrees with §4.1 from a different direction. Writing
seven demos, the constraint that shaped every one of them was the absence of an
aggregate — demo 07 ends with three service names as literals because there is
no list to iterate. Not one demo wanted a memory model, an allocator, or
borrowing. They wanted **a type with two variants and a type with two fields.**

### 4.3 Third: references, borrowing, and the memory model

Q-03 (borrowing), Q-04 (refcount observability) and Q-15 (`str` as `Copy`) are
one question wearing three hats, and Q-15 states the asymmetry that should
decide the timing: **`Copy` → linear breaks every program that duplicates a
string; linear → `Copy` breaks nothing.** So the cheap move is to keep `str`
`Copy` and defer, which is the current state and is correct.

What forces the issue is an owned buffer, i.e. arrays with mutation. Under §4.1
that arrives as a library, so the memory model can be designed against a
concrete client instead of in the abstract. Do not build it before then.

### 4.4 Fourth: concurrency — the one that needs a design first

Q-05 says handlers are a natural fit and the linear/concurrent ownership
interaction is the hard part. D-36 and D-39 have already made the central call
without concurrency being on the table: **no handler captures a continuation**,
so a scheduler cannot be written the way an effect-handler language would write
one. What survives is D-39's route — the multiplicity is **reified as data**
(`par { a } { b }` as delimited blocks the handler schedules) and the resume
points are staged into a state machine.

That is a real design, and it is the *only* one consistent with D-36. It should
be written into `D03` before any code, because getting it wrong reintroduces
continuations, which would falsify D-36, `M10.op_impl`'s shape, and the
inlinability claim of D-23 at once.

### 4.5 Not on the list, but adjacent: the meta-interpreter

`D06` §5 step 1 lists it as blocked on Q-10 (`wenv`/`sig_env` had
function-typed fields). **Q-10 closed** (D-45), so it is no longer blocked — a
fact that survived only in `N02` and is worth stating where the roadmap can see
it. It is nevertheless downstream of §4.1: the interpreter is built out of
lists, and lists are the aggregate that does not exist yet.

---

## 5. What this file is not

Not a decision log. Anything in §4 that gets built moves to `N01` as a `D-`
entry with its reasoning at the time; anything that gets rejected moves to `N02`
as a question with what closing it needs. This file goes stale on purpose and
should be re-read against `N01` before it is trusted.
