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
the reference machine runs it happily. `PUnroll` therefore has no denotation —
not because writing one is hard, but because as typed it does not exist.

*It is now FENCED rather than admitted (D-62).* `M05.uses_unroll` keeps such
terms out of `denote_static`'s domain and the clause is `false_elim ()`, so the
hole no longer conditionalises T3, T4 and T6. That changes nothing about the
question below; it only stops the question from contaminating unrelated
theorems. When this is answered, `uses_unroll` is deleted.

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
*Cost of leaving open:* a fragment of the core that `denote_static` cannot
interpret, and a soundness hole reachable from surface syntax as soon as anything
elaborates to `PUnroll`. Nothing does today.
*Closes when:* recursive types get a surface form.

**Q-14. `!Dict` has to become a real row entry.** — **CLOSED by D-63.**
Reserved as `M04.eff_dict = 0`; `M06.w_eff` derives the entry rather than
trusting a stored one; `M06.row_visible` elides it from rendered rows so nothing
the REPL prints changed. The same edit removed `M07.coherent` outright by giving
`wenv` one signature table instead of two, so T5 is true as originally written.
The worry that it would change what the REPL prints for every `define` did not
materialise — the elision rule D-37 already specified is what prevented it.

**Q-15. Is `str` right to be `Copy` and `Drop`?** `M01.has_cap` gives every
`TPrim` both capabilities, so `PStr` (D-65) duplicates and discards freely. For
an immutable value that is semantically unimpeachable — two copies are
indistinguishable — and it is what makes strings usable without a borrow
checker that does not exist yet.

*What it commits to.* Freely copyable means the implementation must intern or
refcount rather than own a buffer, because an owned buffer duplicated by `dup`
is either a deep copy at every `dup` or an alias. The alternative is to make
`str` a pointer type like `TBox` — linear, explicit `clone`, no `dup` — which is
what Rust does with `String` and which the capability machinery already supports
without a new feature.

*Why it is a question and not a task:* it cannot be settled without the memory
model, and the memory model is not the next thing. Note the decision is CHEAP TO
DEFER in one direction only — going from Copy to linear later breaks every
program that duplicates a string, whereas the reverse breaks nothing.
*Cost of leaving open:* a performance model nobody can state for the one type
every program touches.
*Closes when:* there is an allocator, or `Box`/`Rc` get surface construction.

**Q-16. `handle E { }` discharges `E` from the row while the runtime forwards
the operation outward.** `M06.infer`'s `THandle` rule removes `eff` from the
body's row unconditionally, and `infer_impls` deliberately does not require
every operation of `eff` to be implemented — an unimplemented one forwards to
the next handler out (`M04.fwd_impl`, `R02.find_handler`). So

    handle IO over ( ) init { } { } { "x" print }

typechecks as pure and still prints, and `handle Fail over ( ) init { } { }
{ fail }` types as pure and still escapes.
*Found by:* D-71 — an aborting effect makes the discrepancy trivially reachable,
where before it needed a handler that deliberately omitted an operation. The
gap predates it; `M10`'s H1 already states the proviso in prose.
*What closing it needs:* the rule has to remove `eff` only when every operation
of `eff` is implemented, and to add `eff` back to the row otherwise (the
forwarding case). That is a small change to `infer` and a real change to what
typechecks — `unsafe { … }` and `handle Rec` rely on the effect having no
operations, which stays fine, but a partial handler stops being pure.
*Cost of leaving open:* a row can claim an effect is discharged when it is not,
which is precisely what M09's S5 is supposed to rule out.

**Q-17. Abort discards values without consulting their capabilities.** On a
`fail` the machine cuts the stack back to what `KTry` saved (D-71), dropping the
try block's inputs and everything it had built. Nothing checks that those values
have `CDrop`, so an abort can silently discard a linear value.
*Found by:* implementing `TTry` — the machine's restore is a list truncation and
has no types to consult.
*What a rule would need:* the try block's `pre` and `post` would have to be all
`Drop`, checked in `M06`'s `TTry` rule. That is easy to state and probably too
strong: the point of a linear value is often that the error path must release
it, which wants the catch block to receive it rather than the machine to drop
it. The right answer is likely the same one that gives `catch` an error value.
*Cost of leaving open:* linearity is not yet enforced on the abort path, so a
`Box` in flight when a `fail` fires leaks.
*Closes when:* generics arrive and `catch` can take a typed payload.

**Q-18. `!Dict` or generics first, and what leaves the core when each lands.** —
**CLOSED by D-76 and D-79…D-84.**
Both are specified in D03/D04/D05 and neither exists. They are not independent:
generic instantiation and a capability bound are *Dictionary lookups*, so the
order decides whether generics arrive as a client of existing machinery or as a
second resolution mechanism that later has to be deleted.

*What each removes from the core, which is the criterion that should decide it.*

`!Dict` made dynamic removes duplication rather than constructors:

  * `R02.step`'s two `TWord` paths become one. A `WDef` is inlined straight out
    of the `rdict` today, so a Dictionary frame cannot override a defined word
    at runtime; a `WOp` walks the handler chain. Unifying them is D-60 made
    operational, and it is what `handle Dict { … }` would need.
  * `E04.StWith`'s static substitution pass becomes `THandle eff_dict` followed
    by `TSpecialize` — a derived form instead of a bespoke elaborator case, and
    D-02's claim demonstrated instead of asserted. `M05.subst_words` stays,
    because `specialize` is what uses it.
  * `M10.dict` and `M04.handler` stop being two types for one idea — except
    they cannot actually merge, because `handler.h_ops` is a function field
    (barred from extraction, D-20) and `dict` was de-closured for exactly that
    reason. Merging needs the dependently-typed per-operation table de-closured,
    which D-45 could not do without an existential. **That obstacle should be
    settled before either feature, since both make it worse.**

Generics remove constructors, and rather more of them:

  * **D-56's two-level table.** `PBoxNew`, `PBoxOpen`, `PRcNew`, `PRcClone`,
    `PRcDrop`, `PRcRead` — six of `prim_op`'s fourteen rows — move to a native
    library the moment a library can state `∀T. ( T -- Box[T] )`. This is the
    single largest reduction available anywhere in the spec.
  * With generic NOMINAL types, `TBox` and `TRc` follow their operations out:
    both become `TSeal` declarations carrying their own capabilities, and
    `dtype` drops from six constructors to four. `TSeal` already carries
    `list cap`, so the machinery exists; what is missing is type arguments.
  * `PBoolSum` and `prim.PBool` go when `bool` becomes a declared two-variant
    sum. Strictly this needs surface sums rather than generics, but nobody
    wants sums without `Option[T]`.
  * D-71's two limits close: `catch` takes a typed payload, and `fail` gets
    `∀a. ( -- a )`. Note the core already HAS a bottom type — `TSum []` is
    uninhabited — and its eliminator is already spelled: `absurd` is
    `TDispatch [] []`, which `M06.infer` currently rejects with `Nil? variants`.
    What is missing is not the type but a free result, i.e. exactly generics.

*The conflict to settle first.* D-31 says the language needs no unifier, and
`M03.unify` is prefix matching on concrete segments. Type variables need real
unification. The claim probably narrows to "no unifier for stack rows" with a
separate one over `dtype`, but that is a decision, not a detail, and it should
be made before generics rather than discovered during them.

*Recommendation, taken: `!Dict` first*, on the ground that generic instantiation
is Dictionary lookup and building it first means building a second mechanism to
throw away. The sequence run was `M11.specialize` (D-74), the runtime Dictionary
path (D-75), `with` as a derived form (D-76), D-31 settled as D-77, then generics
(D-79 onward).

*Outcome.* The prediction held, for a reason slightly different from the one
given. Generic instantiation did not turn out to be Dictionary **lookup** — an
instance has no dictionary entry at all (D-83) — but it is Dictionary
**substitution**, `M05.resolve_defs`, which is the function `with` had already
forced into existence. Building generics first would have meant building that
twice, which is what the recommendation was really protecting against.

Of the core reductions listed above, none has been taken; all are now unblocked.
D-56's six `prim_op` rows are the largest and should go first.

*Loose end, independent of both:* **closed by D-78.** `M03.srow_join` was
deleted, along with four dead list traversals in M05.

---

**Q-19. The residual carries one copy of an instance per call site.** — **Half
closed by D-85.** The *work* of building an instance is now shared: identical
instantiations are elaborated once, which took the nesting cost from exponential
to linear (228 s to 27 ms on a depth-10 chain). What is not shared is the emitted
code — `quad quad quad` at `i64` still splices three copies.

The obvious fix, emitting a `WDef` for the shared residual, is the design D-83
deliberately reversed and should not be reached for casually: it reintroduces the
dictionary entry, and with it the ordering constraint that made nested generics
impossible. It would need instance ids allocated BELOW the word being defined,
which means allocating that word's own id after its body is elaborated and
rewriting `recurse` — a real change to D-70's id scheme, and worth doing only
with a measurement behind it.

The cheaper route is what D-85 opened up. Because the cache hands back the
identical term, the copies are now **structurally equal**, so sharing them is
ordinary common-subexpression elimination over the core: a compiler pass, no
elaborator support, and it applies to every inlined term rather than to generics
specifically.

*Closes when:* a CSE pass exists over `M05.term`, or a measurement shows residual
size matters enough to justify the id-scheme change.

**Q-20. A generic body binds its names at instantiation, not at declaration.**
D-85 spells this out because the cache ran into it: a `define` between two calls
of the same generic changes what the second one means, since the stored body is
elaborated against whatever `ne_words` holds at the call.

That is C++'s dependent-name behaviour and it is not obviously what this language
wants. Pinning a schema to the environment of its *declaration* — storing the
name tables in the `gentry` — would make `(name, types)` identify a residual
forever, so the cache could be session-wide, and it is the rule most languages
with generics actually use.

Against it: `!Dict` is deliberately late-bound (D-37, D-75), and `with` exists
precisely so a caller can change what a word means underneath a body. A generic
that ignored rebinding would be the one construct in the language that does.

*Closes when:* it is decided whether a generic body is a closure over its
declaration environment or a template read at each use. Nothing forces it today
because the cache is scoped to one declaration either way.
