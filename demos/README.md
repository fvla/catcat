# demos — the language, doing something

Seven programs. Each is one claim the design makes, run rather than argued.

```
make demos          # run all seven and diff against the golden transcripts
make demos-accept   # regenerate the goldens (read the diff first)

./_build/default/bin/catcat.exe -f demos/03_dictionary_top_down.cat
```

`NN.expected` holds the exact session transcript `NN.cat` produces, so these
are a **regression suite and not decoration**: a change to the elaborator that
alters what a demo prints fails `make demos`. Every claim in
[`DOCS/U03_Tutorial.md`](../DOCS/U03_Tutorial.md) is quoted from one of them.

| | Demo | The claim |
|---|---|---|
| 01 | `01_tour.cat` | it runs — inference, `if`, `recurse`, strings, signatures as assertions |
| 02 | `02_effects_bottom_up.cat` | one program, four `Log` handlers: print, discard, count, capture. **D-01** |
| 03 | `03_dictionary_top_down.cat` | `with` and `handle Dict` reinterpret code not written for it; a profiler over untouched words |
| 04 | `04_generics_and_staging.cat` | a generic is `specialize` run early; the residual shows monomorphization. **D-02** |
| 05 | `05_mocking_c.cat` | `extern` + `handle C`: a deterministic test of code that calls libc |
| 06 | `06_failure.cat` | `try`/`catch` as a handler for `Fail`, composing with the rest |
| 07 | `07_three_modes.cat` | **capstone** — one deploy script, run as production, dry run and audit |

Start at 07 if you want the point in one file, at 01 if you want the language.

## Reading the transcripts

The whole file is fed to the REPL, split on **blank lines**, one paragraph per
line — so `\` comments become narration and the golden file reads top to bottom
as a session. `catcat> ` marks what was fed in; everything else came back.

Errors are on purpose. A demo that only showed what works would be hiding the
half of the design that lives in what gets rejected, so each file deliberately
runs the failing cases too, and the goldens record the messages.

## What they deliberately do not show

There are no arrays, no lists, no records and no string indexing, so every demo
is control- and effect-shaped rather than data-shaped. Demo 07 ends with three
service names written out as literals for exactly this reason. That ceiling and
what it will take to lift it are in
[`NOTES/N04_Roadmap.md`](../NOTES/N04_Roadmap.md) §4.1.

## Gaps these found

Writing them turned up four things worth having in the record, all now tracked:

- **`with` does not reach into a generic instance** (N02 Q-21). An instance is a
  `TSpecialize`, which resolves its calls where it stands, so a caller's
  rebinding arrives too late. Demo 04 shows it.
- **A `try` block runs on a fresh stack and cannot see a local**, which is what
  stops `try` being usable in the obvious way. Demo 06 leads with it.
- **A handler implementing none of its operations still discharges the effect**
  (N02 Q-16). Demo 02 ends with a word that typechecks as pure and escapes.
- **`U01` §4 and §6 contradicted each other** on whether recursion exists, and
  `U01` §6's `!Rec` propagation example predated the bare-`!` rule (D-77). Both
  fixed.
