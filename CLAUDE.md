# catcat — working notes for Claude

**catcat**: con*cat*enative, *cat*egorical. A statically stack-typed concatenative
language with algebraic effects, staged compilation, and a mechanized core in F*.

Read this file first. It says where everything is, what the conventions are, and
how to work on this project without re-deriving context.

---

## Orientation: read these, in this order

1. `P00_Design/D01_Overview_and_Goals.md` — goals, feasibility, the two central
   ideas. **If you read one file, read this one.**
2. `NOTES/N01_Decisions.md` — the decision log. Every settled design question
   with its reasoning. Check here before proposing anything; it is probably
   already decided.
3. `NOTES/N02_Open_Questions.md` — what is deliberately unsettled.
4. `P00_Design/D02`–`D06` — the design proper.
5. `DOCS/U01_Grammar.md`, `U02_Word_Reference.md` — the language **as it runs**,
   which is a strict subset of the above. Fastest way to see the real gap.

The two ideas everything else follows from, so you have them immediately:

- **Effects, interfaces, traits, classes, modules and the Dictionary are ONE
  construct.** Not by analogy — one `handler` record in `M10_Handlers.fst`.
- **Compile-time specialization and runtime JIT are the SAME operation**,
  `specialize`, differing only in when it runs. One theorem covers both.

---

## Layout

Directories are numbered so dependency order and reading order coincide. Files
within them likewise. Proofs read top to bottom; so does this project.

| Path | What | Status |
|---|---|---|
| `P00_Design/` | `D01`–`D06`, prose design specification | current |
| `P01_Specification/` | `M01`–`M11`, mechanized core in F* | M01–M06 complete, M07–M11 skeletons |
| `P02_Reference/` | `R01`–`R06`, reference interpreter | runs; extracts to OCaml |
| `P03_Elaboration/` | `E01`–`E05`, lexer → parser → elaborator → REPL | **REPL works**; subset of D05 |
| `DOCS/` | `U01`–`U02`, user-facing docs for the language as it runs | current |
| `NOTES/` | decision log, open questions, session handoff | current |
| `.claude/skills/` | project skills | `delegate` |
| `bin/`, `generated/` | OCaml glue and extraction output | generated — do not hand-edit |
| `P01_Specification-old/` | abandoned first attempt | **dead, do not read for guidance** |
| `INITIAL_DRAFT_1.md` | original vision doc | historical |

`P01_Specification-old/` and `INITIAL_DRAFT_1.md` are now committed, so deleting
them is recoverable — but still don't, without being asked. Neither is a guide.

**Commit as you go.** The user asked for this; do not leave a session's work
uncommitted. `make verify` must pass first.

Planned, not yet created: `P03_Elaboration/`, `P04_Compiler/`, `P05_Backend/`,
`P06_Tooling/`.

---

## Commands

```
make verify        # typecheck P01 + P02 + P03. Must pass before any commit.
make verify-spec   # P01 only
make verify-ref    # P02 only
make verify-elab   # P03 only
make catcat        # build the REPL  -> ./_build/default/bin/catcat.exe
make interp        # extract, build, run the core example programs
make admits        # inventory every admit / assume val
make repl          # the original template binary; keep it building
```

`make verify` from a clean cache takes a couple of minutes. `make interp` checks
the spec produces a working evaluator; `make catcat` gives you the REPL, which
also runs non-interactively for scripted tests:

```
./_build/default/bin/catcat.exe '2 3 +' 'define sq { dup * }' '6 sq'
```

Planned, not yet created: `P04_Compiler/`, `P05_Backend/`, `P06_Tooling/`.

---

## Conventions that will bite you

**No lookahead, lexer or parser** (D-30). The scanner is a plain DFA — every
branch is a predicate on the one character in hand — and the parser is LL(1).
This is a hard constraint: the planned verified CFG-to-recursive-descent
generator cannot describe a grammar that needs lookahead. Any syntax that needs
a second token to disambiguate is rejected on these grounds. It is what killed
the self-delimiting `--` (D-28, reverted), so check here before "fixing" a
lexing surprise with a special case.

**Stack order.** The head of a core index list is the TOP of the stack. Surface
signatures use the Forth convention and read bottom-to-top, top on the RIGHT.
Elaboration reverses them. The abandoned draft got this wrong in a way that took
a while to see — state the convention at every boundary.

**F\* mutual recursion needs explicit lexicographic measures.** A plain size
measure is non-strict on list-to-element edges. The working pattern, used in
M01, M05 and M06:

```fstar
let rec f (t:term) : Tot bool (decreases %[(term_size t <: nat); 0]) = ...
and     g (ts:list term) : Tot bool (decreases %[terms_size ts; 1]) = ...
```

Rank orders `list(1) > element(0)`; acyclic because every element-to-list edge
strictly decreases size. Ascribe `<: nat` when one measure returns `pos`.

**`*` is the tuple type constructor**, not multiplication, unless `FStar.Mul` is
open. Use `&` for tuples. This produces a baffling "expected Type, got int".

**`.fsti` makes definitions opaque.** A definition *given* in an interface stays
transparent; one only `val`-declared does not. P02 has interfaces; **P01
deliberately does not** — M07's `denote` needs `infer env TNil` to reduce, so
interfacing M06 breaks the build. Do not add interfaces to P01 without checking
this.

**Implementation order must match interface order** in an `.fst`/`.fsti` pair.

**Extraction needs one invocation per implementation.** A module with an
interface has only its `.fsti` loaded by dependents, so a single whole-program
extraction emits nothing for the bodies. See the `generated/R05_Driver.ml` rule.

**Every `admit` and `assume val` carries a comment** saying what discharging it
requires. `make admits` is meant to be a readable inventory. Do not add a bare
one.

**Never write `Lemma True` as a placeholder.** A stub that proves nothing while
looking like a lemma is worse than an honest gap. State the obligation in prose
instead — see the bottom of `M07_Denotation.fst`.

---

## Working style for this project

- **The spec is the source of truth.** F* first, then extraction. Do not write
  OCaml or catcat by hand that F* could generate.
- **`make verify` is the acceptance test.** Not review, not plausibility.
- **Keep P02 in the first-order subset.** No closures, no higher-order
  functions, no function-typed record fields. The rules are in
  `R01_Runtime.fsti`'s header. Violating them silently blocks self-hosting and
  no OCaml test will catch it.
- **Record decisions in `NOTES/N01_Decisions.md` as you make them**, not at the
  end. A future thread starts from that file.

## Documentation hygiene

`DOCS/` describes the language **as it actually runs**, which is a different job
from `P00_Design/` — that describes the language as designed. The two drift, and
the whole value of `DOCS/` is that a reader can tell which they are holding.

Two rules, mandatory for every file in `DOCS/`:

1. **Stamp the commit.** Each file carries `**Current as of commit `<hash>`.**`
   near the top. Update it whenever you touch the file; a doc with a stale hash
   is at least honestly stale, whereas an unstamped one is just wrong.
2. **Point at the source of truth.** Name the specific files — and where useful
   the specific functions — the doc is derived from, and say plainly that the
   source wins on disagreement. A user doc is a cache, not an authority.

Then, when writing:

- **Verify claims against the running binary**, not against the design docs or
  your memory of the code. Every table entry in `U01`/`U02` was checked by
  running `catcat.exe`. This is how the `!Eff`-silently-discarded and
  no-`true`/`false` gaps were found.
- **List what is missing.** `U01` §5 exists because the gap between D05 and the
  implementation is otherwise invisible to a reader, and gaps that mislead —
  like a signature accepting `!IO` and dropping it — get called out as such.

## Delegating

**Default: do it yourself. Sonnet delegation is disabled for cost reasons.**
Haiku is allowed only for short, mechanical, concurrent tasks, prompted raw
with no project context.

The reason is prompt caching: your conversation context is cached at roughly a
tenth of normal input cost, so a file you already hold is nearly free for you to
touch and full price for a cold subagent to re-read. Hence:

> Delegate work whose input you do NOT already hold.
> Do work yourself whose input is already in your context.

Read the `delegate` skill before spawning anything — it has the policy, the raw
Haiku prompt skeleton, and what would justify re-enabling Sonnet.
