# N02 — Open questions

Deliberately unsettled. Each entry says why it is open and what would close it.
Moving one to `N01_Decisions.md` is how it gets closed.

---

**Q-01. Debug reinterpretation vs type erasure.** (D-24)
`R04_Erasure` discards exactly the information a debugger needs to reinterpret a
running program under different rules — a stated D01 goal.
*Options:* a side table from stack position to static type; or make erasure a
parameterised pass with a retain-indices debug mode.
*Closes when:* P06 tooling work starts, or earlier if the side table turns out to
be needed by the compiler anyway.
*Cost of leaving open:* low now, high if discovered during P06.

**Q-02. Deep-handler typing with explicit continuations.** — **CLOSED** by
decision (D-36). No handler captures a continuation, so there is nothing extra
to type. `M06.THandle` checks implementations against the operation's declared
signature framed by the handler's state, which is now the complete rule rather
than a rule that covers the easy cases.

**Q-12. Handler state aliasing is checked at runtime, not statically.**
`R02` blanks a handler frame's state while an implementation runs, and an
operation that reaches the same frame meanwhile gets stuck (D-48). That is a
dynamic borrow check in a language whose whole linearity story is static.
*Found by:* implementing stateful handlers — the case falls straight out of
"the state is lent to the implementation".
*What a static rule would need:* the effect row of an implementation would have
to exclude the effect its own handler handles, which is expressible in the row
system as it stands. It is not obviously the right rule — mutual recursion
between two operations of the same effect is a legitimate thing to want, and it
needs the state passed along rather than re-borrowed.
*Cost of leaving open:* a program that does this fails loudly rather than
silently, which is the acceptable direction.

**Q-03. Borrowing.**
Reading through an `Rc` currently requires a `Copy` payload (`PRcRead`). Reading
a non-`Copy` payload without consuming needs borrows, which is a whole feature.
*Closes when:* someone needs a non-`Copy` payload behind a shared pointer.
Deferring is fine; `Copy` payloads cover the common cases.

**Q-04. Refcount observability.**
The reference interpreter models `Rc` by direct nesting with no count. Sound
while payloads are immutable — the count only decides *when* a destructor runs,
and the interpreter has no observable deallocation.
*Reopens if:* interior mutability or observable destruction is added.

**Q-05. Concurrency.**
Listed as a built-in effect (D03 §7), unspecified. Handlers are a natural fit;
the interaction between linear types and concurrent ownership is the hard part.

**Q-06. Numeric tower.**
M01 uses mathematical bounded integers and abstract floats. Wrapping,
saturation, IEEE-754 are properties of *operations* and need a module M01 does
not have. The reference interpreter deliberately implements no float arithmetic
rather than inventing an answer.

**Q-07. Dependent types.**
Lowest priority, correctly. Nothing forecloses them, but `TSeal` would need to
become environment-relative first — which D-25 partly does anyway.

**Q-08. `'…'` quotation.**
Reserved, recommended, uncommitted. Natural reading: `'word` is `{word}` for a
single word.

**Q-10. `wenv` and `sig_env` have function-typed fields.** — **CLOSED** (D-45).
Both are association lists with total lookup functions (`M04.op_of`,
`M04.eff_of`, `M06.w_sig`, `M06.w_eff`). `E06_Repl` no longer builds a closure
and P03 is inside the first-order subset throughout.

What made this worth doing ahead of the effect system rather than as cleanup:
`mk_wenv` had been faking the operation table, returning a nullary signature
for every id, because there was no honest way to build one. Handler
typechecking reads that table. The fake would have silently accepted every
handler implementation.

**Q-11. Inline signature display in the editor.** (D-31)
Every word's stack effect is now computed whether or not it is written down, so
the language server can render it at the definition and at call sites — the
direct answer to a stack language's central readability problem, and it cannot
go stale because it is not a separate artifact.
*Open part is presentation, not computation:* inlay hint vs. gutter vs.
hover-only; whether to show inferred signatures on words that already declare
one; and whether to show the *incremental* effect mid-body, which is the version
that would actually help while writing.
*Wants:* source spans in the lexer (E03's header notes they are absent), so a
signature can be attached to a position.
*Closes when:* P06 starts.

**Q-09. Subset conformance is unchecked.**
P02's first-order discipline (D-20) is maintained by review. A single accidental
closure silently blocks self-hosting and no OCaml test catches it.
*Closes when:* someone writes a syntactic pass over the extracted AST.
*Cost of leaving open:* grows with every P02 module added.

**Q-13. `TName` roll/unroll is unsound, and closing it needs a value-level
invariant.** Found by writing `M07.prim_den`: `M06.prim_sig` asks only for
`wf d`, so `PRoll n d1` followed by `PUnroll n d2` typechecks for any well-formed
`d2` and reinterprets a `d1` as a `d2`. `R02.apply_primop` makes both no-ops, so
the reference machine runs it happily. `PUnroll`'s denotation is therefore
`admit ()` — not because it is hard, but because as typed it does not exist.

*Two halves, and the second is the question.* The typing half is routine and
already flagged as a LIMITATION at `prim_sig`'s `PRoll` clause: `wenv` gains
`w_types : list (nom_id & dtype)`, `prim_sig` starts taking an environment, and
both rules require `d == lookup w_types n`. The value half is not routine.
`M02.VName #n #t v` hides the payload's type as an implicit index, so no amount
of typing discipline lets anyone project `t` back out. Either

  * `VName` stores its body type as an explicit field and `vunroll` becomes
    decidably partial — cheap, but reintroduces a runtime check for something the
    type system was supposed to have settled; or
  * `value` gains a well-formedness predicate tying every `VName` to `w_types`,
    threaded as a precondition through M07 — honest, but it is precisely the
    invariant-restoring obligation `M02`'s header claims to have abolished, and
    it would be the first one back.

*Why it is a question and not a task:* the second option costs M02 its central
property, and the first quietly admits that incomplete types are dynamically
checked. That is a design call.
*Cost of leaving open:* one admit, and a soundness hole reachable from surface
syntax as soon as anything elaborates to `PUnroll`. Nothing does today.
*Closes when:* recursive types get a surface form.

**Q-14. `!Dict` has to become a real row entry.** D-37 settled that a word's
meaning depends on the dictionary it was elaborated against and that `!Dict` is
the encoding of that fact — then left it implicit, on the stated grounds that
`M04.within` never sees it. `M07.denote_static` makes `within` see it: `TWord w`
denotes `Op w`, so a word with an empty row performs an operation its row does
not mention, and M07's T5 is false as written.

*The fix is known and small; what is open is when to pay for it.* Reserve an
`eff_id` for `Dict`, have `M06.w_eff` return it for any word that is not a
declared operation, and register defined words in `w_ops` under it — which is
also what `M07.coherent` needs from P03, so one change closes both. It is
deferred only because it changes what the REPL prints for every `define`, and
`DOCS/U01`–`U02` claim otherwise.
*Closes when:* T5 is discharged, or sooner if signature rendering is revisited.
