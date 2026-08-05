# N03 — Session log and handoff

Where things stand. A new thread should read `CLAUDE.md`, then
`NOTES/N01_Decisions.md`, then this file, and be able to continue.

---

## Current state

| Phase | Status |
|---|---|
| `P00_Design/` D01–D06 | current |
| `P01_Specification/` M01–M11 | M01–M06 complete; M07–M11 skeletons with obligations recorded in place |
| `P02_Reference/` R01–R06 | runs; extracts to OCaml; `make interp` evaluates the example programs |
| `P03_Elaboration/` E01–E05 | **REPL works** — `make catcat`; lexer, parser, elaborator, session |
| `P04`–`P06` | not started |

`make verify` passes on everything (28 modules). `make admits` lists 12 gaps,
**all in P01** — P02 and P03 have none.

### What the REPL does today

```
catcat> 2 3 + 4 *
ok  20
catcat> define sq { dup * }
defined sq ( i64 -- i64 )
catcat> 6 sq
ok  20 36
catcat> define hypotsq { sq swap sq + }
defined hypotsq ( i64 i64 -- i64 )
```

Full pipeline per line: lex → parse → elaborate → **M06 typecheck** → evaluate
on the R02 machine. A parse or type error leaves the session untouched. It also
runs non-interactively (`catcat.exe 'line' 'line' …`), which is the regression
harness.

**Implemented subset of D05:** integer and boolean literals, words with
free-form names (so `+`/`*`, D-32), `define` with a signature *or* with the
signature inferred (D-31), named parameters `$x:i64` with the suffix rule,
`dup`/`pop`/`swap` instantiated from the compile-time shape, `Box[]`/`Rc[]` type
syntax, `\` line comments, self-delimiting brackets.

**Deliberately absent, each already specified in D05:** macros, modules and
`::`, generics `[]`, effect rows and handler syntax, sums and classes, strings,
`let` and its destructuring form, `.` member access.

### The 12 admits, and the order to attack them

1. `M03.lemma_compose_assoc` — signature composition is associative. Four-way
   case analysis on which segment runs out; closes by `append_assoc` and
   `lemma_unify_disjoint`. **Do this first**: M07's `denote` needs the same
   transport reasoning.
2. `M04.lemma_fbind_right_id`, `lemma_fbind_assoc` — true, but need functional
   extensionality in the `Op` case. Requires restating `free`'s continuation
   over `FStar.FunctionalExtensionality.(^->)`. Mechanical but invasive; doing
   it early avoids redoing the M07 inductions.
3. `M07.denote` (`assume val`) plus `thm_denote_nil`. The `TSeq` clause is the
   only hard case.
4. `M08.step`, `M10.handle` — do these **together**; the handler-frame
   representation is shared and should not be guessed twice.
5. `M09.state_typed`, `M11.specialize` / `specialize_typed` / `stage_required`.

---

## Session: 2026-07-27

### Done

- **P02 reference interpreter built and running.** Defunctionalised CEK machine,
  first-order throughout so it can extract to catcat as well as OCaml. Verified,
  extracted, and evaluating arithmetic, sealed classes, sums, and handled and
  unhandled effects.
- **Recursive types added** (D-25). `TName`/`TBox`/`TRc` in M01, values in M02,
  eight terms in M05, typing in M06, runtime in R01–R05. This unblocked
  self-hosting.
- **Project infrastructure**: `CLAUDE.md`, `NOTES/`, and the `delegate` skill.

### Found by building, not by review

Two things surfaced only because an artifact was actually constructed. Worth
noting as a pattern — the design docs had been reviewed repeatedly and neither
appeared.

- **catcat could not express recursive types.** Found by attempting the catcat
  encoding of the interpreter's own data types in R06. Every `dtype` case was
  structural and finite. The interpreter ran fine because its data lived in
  OCaml; only the catcat-hosted version needed it, which is exactly why review
  missed it. Fixed this session.
- **`.fsti` on P01 would break the build.** Found by testing rather than
  assuming: a definition given in an interface stays transparent, one only
  `val`-declared does not, and M07's `denote` needs `infer env TNil` to reduce.
  See D-22.

### Delegation: first run

Three Sonnet workers in parallel for the Box/Rc tail, after the core chain
(M01 → M02 → M05 → M06 → R01) was done directly.

**What the split taught.** The naive plan — one worker per file — would have
failed here, because most of this change is a dependency chain. The working
split was: do the chain yourself, fix the contracts, then fan out only the
genuinely independent tail. That generalises, and it is now written up in the
`delegate` skill as the core technique: **split along interface boundaries, not
along dependency chains.**

For P03 this means writing the `.fsti` files first, then one worker per `.fst`.

**Shared-tree hazard, found the hard way.** Workers edit one checkout and
`make verify` is global, so a worker running it while a sibling is mid-edit
sees failures in files it never touched. One worker hit exactly this — an
incomplete pattern match in a file another worker was halfway through — and
reported it as "SMT-solver flakiness". It was neither flaky nor the solver.
Mitigation is now in the skill: warn workers, have them verify their own module,
and treat the orchestrator's final `make verify` as the authoritative one.

Generalisable lesson: **"transient" or "flaky" in a worker's report is a flag to
look harder, not reassurance.** A plausible-sounding misdiagnosis is the failure
mode to watch for when reviewing delegated work.

**Outcome: Sonnet delegation is now disabled (D-27).** The run cost roughly
1.5–2× doing it directly and bought only wall-clock time. The mechanism is
prompt caching — the orchestrator's context is cached at roughly a tenth of
normal input cost, so files already in context are nearly free to touch and
full price for a cold subagent to re-read. Every file in this run had been
authored minutes earlier, making it the worst possible case. Haiku remains
available for short mechanical sweeps, prompted raw. The interface-boundary
split was still the right *shape*; it just cannot overcome the cache asymmetry
when the contracts were written moments before.

---

## Next

In order. Steps 1–2 are small and unblock the rest.

1. **`M03.lemma_compose_assoc`.** See above.
2. **Add a declaration environment to `wenv`** — a `w_decl : nom_id -> dtype`
   field, so M06 can check `PRoll n d` against what `n` actually declares.
   Currently unchecked, and it is the one remaining hole in the recursive-type
   work. Small, and it is the last place a type environment is needed.
3. **Write the catcat encodings** in R06 (`enc_rvalue`, `enc_term`, `enc_kont`).
   Now expressible; nobody has written them.
4. **P03 elaboration.** `.fsti` contracts first, then fan out. Design errors in
   D05 — the named-parameter suffix rule, `let` destructuring order — are far
   cheaper to find against the interpreter than after codegen exists.
5. **Subset conformance checker** (N02 Q-09). A syntactic pass over the
   extracted AST. The cost of not having it grows with every P02 module.

## Session: P03 and the REPL

Two things surfaced by building, again — the pattern from the previous session
repeated exactly.

- **`dup`/`pop`/`swap` cannot express locals.** They reach only the top two
  slots and no composition of them touches a third, so `$x` was unimplementable
  until `pick`/`roll` were added to the core (D-29). Design review had not
  caught it; writing the elaborator did, immediately.
- **`--` was not self-delimiting.** `( i64--i64 )` lexed as one word while
  `{$x $x mul}` worked. Fixed as D-28.
- **`wenv` has function-typed fields**, so the REPL's `mk_wenv` is a closure and
  the only first-order-subset violation in P03 (N02 Q-10).

Everything else in the pipeline went in cleanly. The recurring F* frictions were
the known ones from `CLAUDE.md`: `*` needing `FStar.Mul`, and mutual recursion
needing explicit lexicographic measures — plus one new one worth knowing:
**parser combinators need `decreases (length ts)`, not a structural measure**,
because a remainder returned by a sub-parse is not a subterm of the input.
Carrying a `length` refinement on every parse result is what makes that work.

## Session: inference, operators, and the no-lookahead rule

Three changes, and the second is the interesting one.

- **Signature inference** (D-31). `define sq { dup * }` infers `( i64 -- i64 )`.
  Cheap for the structural reason in D-31: concatenative composition *is*
  signature composition, so it is one walk with a flat substitution and no
  unifier. Implemented as two passes in E04 — pass 1 types, pass 2 is the
  existing concrete elaborator re-run with the answer.
- **D-28 reverted.** `--` is a space-separated word again. It had been made
  self-delimiting to fix `( i64--i64 )`, but stating D-30 showed that special
  case *was* the lexer's only lookahead, and that the arrow being exempt from
  the space rule was the real inconsistency. Deleting it made the scanner a
  plain DFA.
- **Operators** (D-32). `+ - * / % < <= =` replace `add`/`mul`/`lt`. No lexer
  change was needed — word names were already free-form.

**Worth carrying forward:** the first fix for a lexing surprise is usually a
special case, and the special case is often the thing causing the surprise.
D-28 survived one session precisely because nobody had written down D-30; once
the invariant was explicit, the exception was obviously the bug. **State the
invariant and the wrong special case falls out on its own.**

## Repository hygiene

The project is committed, and from this session on **changes are committed as
they are made** — the user asked for this explicitly.

`.gitignore` already covers `generated/*.ml` and `*.mli` (extraction output,
regenerated by `make interp` and `make catcat`), plus `_build/` and
`.fstar-cache/`. The earlier note here claiming the `M0*`/`R0*` outputs were
unignored was wrong; the glob covers them.

## Do not

- Delete `P01_Specification-old/` or `INITIAL_DRAFT_1.md` unasked. Both are now
  committed, so it is recoverable — but neither is a guide, and the old spec's
  approach was abandoned for the reasons in D-03.
- "Fix" a lexing or parsing surprise by adding a special case without checking
  D-30 first. That is exactly how D-28 happened.
- Add `.fsti` to P01 without re-checking D-22.
- Write P04's IR against `dtype` before step 2 above is settled.
