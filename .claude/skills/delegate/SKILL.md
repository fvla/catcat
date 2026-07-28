---
name: delegate
description: Delegation policy for the catcat project. Sonnet delegation is DISABLED for cost reasons; Haiku is allowed only for short, mechanical, concurrent tasks, prompted raw. Read this before spawning anything.
---

# Delegating work on catcat

**Default: do it yourself.** Delegation on this project lost money on its first
real trial, and the reason generalises. Read §1 before spawning anything.

## 1. Why the default is "do it yourself"

Your conversation context is **prompt-cached at roughly a tenth of normal input
cost**. A file you already hold is nearly free for you to touch. A subagent
spawns cold and pays **full price** to read that same file.

So the rule is not about task size or file count:

> **Delegate work whose input you do NOT already hold.
> Do work yourself whose input is already in your context.**

Measured on the one run so far (three Sonnet workers, Box/Rc implementation):
~194k subagent tokens against maybe 35k had it been done directly — roughly
**1.5–2× the cost** once weighted for Sonnet's cheaper per-token rate and the
fact that subagent spend is mostly input. It bought wall-clock time, nothing
else. Every file involved had been authored minutes earlier and was sitting in
cache.

Corollaries worth internalising:

- **Delegate reading, not writing.** Search, audit, and exploration *compress*
  — large input, small output — and the orchestrator never loads the input.
  Authoring *expands*, and the worker must load context before it can write
  well. Compression is what subagents are actually for.
- **Count workers, not files.** Each worker pays a fixed orientation cost
  (~15–20k tokens here) before doing anything useful. Three workers pay it
  three times. One worker doing three tasks pays it once.
- **Never write a long brief AND let them read.** That is double payment, and
  it is what happened on the first run. Either write a minimal brief and let
  them read, or write a complete self-contained brief and forbid reading.
- **The one case where delegation is an enabler, not an optimisation:** total
  input exceeds your context window. Then doing it yourself means compaction
  and lost fidelity, and a subagent is the only way to keep it.

## 2. Current policy

**Sonnet delegation: DISABLED.** Do not spawn Sonnet subagents. This is a
standing cost decision, not a judgment about capability — Sonnet's work on the
trial run was correct. If a task genuinely seems to need it, say so and let the
user decide rather than spawning.

**Haiku: allowed, narrowly.** Only for work that is *all* of:

- **Short** — minutes, not tens of minutes.
- **Mechanical** — one known pattern applied repeatedly; no design judgment.
- **Concurrent** — 3+ genuinely independent units, or a directory sweep.
- **Self-contained** — expressible in a brief with no project background.
- **Over input you do not already hold** — otherwise do it yourself (§1).

Good Haiku work: renaming a symbol across many files; reformatting; collecting
an inventory ("list every file containing X and the line number"); checking a
mechanical property file-by-file; extracting a table from many documents.

**Never give Haiku:**

- **F\* proof work.** Termination measures, lexicographic `decreases` clauses,
  SMT failures. It will flail and burn more than it saves.
- Anything requiring a design decision, or judgment about what the user wants.
- Anything where being confidently wrong is expensive and hard to notice.

**Opus:** do it yourself. Never spawn Opus.

## 3. Prompting Haiku raw

Subagents already start cold — they do **not** inherit your conversation, so
there is nothing to strip. "Raw" here means keeping the brief minimal on
purpose:

- **Do NOT point at `CLAUDE.md`**, the design docs, or the notes. Mechanical
  work does not need project context, and loading it is most of the cost.
- **Do NOT explain the design rationale.** State the transformation.
- **Give the exact file list.** Absolute paths. Do not make it search.
- **Give the exact pattern**, ideally with a before/after example.
- **Give one cheap acceptance check** — the narrowest command that proves the
  change, not `make verify` over the whole project.
- **Cap the report**: "Report in 5 lines or fewer: files changed, check result,
  anything ambiguous."

Skeleton:

```
In /home/frederick/git/catcat, in these files ONLY:
  <absolute paths>

Replace <exact old form> with <exact new form>.
Before: <example>
After:  <example>

Do not change anything else. Do not read other files.

Verify with: <one narrow command>
Report in 5 lines or fewer: files changed, check result, anything ambiguous.
```

Put independent spawns in **one message** so they run concurrently.

## 4. Reviewing what comes back

- **Run the real check yourself.** Workers verify narrowly; only you run
  `make verify` on the integrated result.
- **Treat "transient" and "flaky" as flags to look harder.** On the trial run a
  worker reported an incomplete pattern match in a file it never touched as
  "SMT-solver flakiness". It was neither — a sibling was mid-edit and
  `make verify` is global across one shared checkout. A plausible-sounding
  misdiagnosis is the failure mode to watch for.
- **Warn about the shared tree** whenever more than one worker runs at once: a
  failure outside their brief is probably a sibling mid-edit, so re-run once
  before investigating.
- **Check `make admits` didn't grow.** A worker that "finished" by admitting a
  lemma has not finished.

## 5. What would justify re-enabling Sonnet

Record the reasoning if this is revisited, rather than just flipping it back.
The case would need at least one of:

- **Input you don't hold.** A sweep or audit across a large body of code that
  is not in your context — where the worker's output is a small summary.
- **Context-window pressure.** Work whose inputs would not fit, so delegation
  preserves fidelity rather than costing extra.
- **Wall-clock genuinely mattering more than cost**, stated by the user for
  that specific task.

Interface-boundary splitting (write the `.fsti` yourself, fan out the `.fst`
bodies) remains the right *shape* for parallel F\* work if it is ever re-enabled
— it was the sequencing that worked on the trial run. It just doesn't overcome
the cache asymmetry when you already hold the contracts you just wrote.
