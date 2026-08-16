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

| # | Demo | The claim it demonstrates |
|---|---|---|
| 01 | tour | it runs: inference, `if`, `recurse`, strings, signatures as assertions |
| 02 | effects, bottom-up | one program, three `Log` handlers: print, discard, count. D-01 |
| 03 | dictionary, top-down | `with` and `handle Dict` reinterpret code that was not written for it; a profiler over untouched words |
| 04 | staging | `with` is discharged at elaboration and `handle Dict` at runtime; **same answer, different residual**, shown with `locate`. D-02 |
| 05 | mocking C | `extern` + `handle C`: a deterministic test of a program that calls libc |
| 06 | generics | explicit instantiation, generics calling generics, and the residual showing specialization happened |
| 07 | failure | `try`/`catch`, and `Fail` composing with the other effects |

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

### 4.1 First: aggregates, via the F\*-library route — the real unblocking

`Box` and `Rc` already exist in `M01.dtype` and their six operations
(`PBoxNew`, `PBoxOpen`, `PRcNew`, `PRcClone`, `PRcDrop`, `PRcRead`) are six of
`prim_op`'s fourteen rows. D-56 says they leave the core the moment a library
can state `∀T. ( T -- Box[T] )`. **Generics now exist** (D-79…D-85), so the
blocker named in Q-18 is gone and this is the largest single reduction available
anywhere in the spec.

It is also the same work as "libraries implemented in F\* that extract to
catcat", which is why it comes first. The full `emit : <F* subset> -> term` of
`R06` §1 is a metaprogramming project; the useful 80% is not. A catcat program
*is* a value of `M05.term`, so an F\*-checked library is an F\* module that
**produces `term`s and signatures directly** and a session pass that installs
them. No pretty-printer, no parser round-trip, no reflection on F\* syntax —
`R06` §1's own argument for why the AST is the artifact applies at this scale
too. That is a tractable module (call it `P02_Reference/R07_Library.fst` or a
new `P04`), and once it exists:

- `Box`/`Rc` move out of `prim_op` and `dtype` drops from six constructors to
  four (`TBox`/`TRc` become `TSeal` declarations with type arguments);
- an **array** type becomes a library declaration rather than a core change,
  which is the only version of arrays worth building — an array in the core
  would be a seventh and eighth `prim_op` block with no proof story;
- `bool` can become a declared two-variant sum, removing `PBoolSum` and
  `prim.PBool`;
- `fail` gets `∀a. ( -- a )` and `catch` a typed payload (D-71's two limits).

So **arrays and memory management are downstream of the library mechanism, not
of a memory model.** That is the non-obvious conclusion of this section and the
reason it is first.

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
