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

**Q-02. Deep-handler typing with explicit continuations.**
M06's `THandle` rule checks implementations against the operation's declared
signature. Correct for interface/class methods and handlers that resume exactly
once; insufficient for handlers that capture and reuse the continuation, which
need it in their signature.
*Closes when:* M10's semantics are written.

**Q-03. Borrowing.**
Reading through an `Rc` currently requires a `Copy` payload (`TRcRead`). Reading
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

**Q-10. `wenv` and `sig_env` have function-typed fields.**
`M06_Typing.wenv` is `{ w_sig : word_id -> srow; … }` and `M04_Effects.sig_env`
likewise. Constructing one needs a closure, which breaks the first-order subset
(D-20) — so `E05_Repl.mk_wenv` is currently the only subset violation in P03,
and it blocks catcat-extraction of that module.
*Found by:* writing the REPL, which must build a `wenv` to call `infer`.
*Fix:* change both records to association lists in P01, and add lookup helpers.
Mechanical, but it touches the spec, so it wants doing deliberately rather than
in passing.
*Cost of leaving open:* nothing today — the OCaml build is unaffected. It
becomes blocking when P03 needs to self-host.

**Q-09. Subset conformance is unchecked.**
P02's first-order discipline (D-20) is maintained by review. A single accidental
closure silently blocks self-hosting and no OCaml test catches it.
*Closes when:* someone writes a syntactic pass over the extracted AST.
*Cost of leaving open:* grows with every P02 module added.
