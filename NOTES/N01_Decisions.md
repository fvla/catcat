# N01 — Decision log

Settled design questions, newest section last. **Check here before proposing
anything**; it is probably already decided. Each entry says what was decided and
why, because the reasoning is what a future thread needs.

---

## Core shape

**D-01. Effects, interfaces, traits, classes, modules and the Dictionary are one
construct.** Not an analogy — one `handler` record in `M10_Handlers.fst`. The
roles differ only in when the handler resolves and whether it is erased.
*Why:* one thing to learn, one thing to optimize; making static dispatch free
makes all six free at once.

**D-02. Compile-time specialization and runtime JIT are one operation.**
`specialize(program, dictionary)`, differing only in when it runs. One
correctness theorem (M11 E2) covers both.
*Why:* no second trusted path from source to machine code, so the usual JIT
failure mode — interpreter and compiled path drifting apart — is structurally
excluded.

**D-03. Intrinsic stacks, not refined lists.** `vstack` is an inductive family
indexed by `list dtype`.
*Why:* the abandoned draft refined `list value` by a `splitAt` predicate and
spent all its effort proving things about `splitAt`. Intrinsic typing reduced the
entire structural burden to two lemmas, and made the frame property one
combinator with one lemma instead of a per-definition obligation.

**D-04. Signatures are implicitly row-polymorphic.** The row variable is never
written in the core; `frame` recovers it.

**D-05. Head of a core index list is the TOP of the stack.** Surface signatures
use the Forth convention (bottom-to-top, top on the right); elaboration
reverses. *Why the mismatch:* `( a b -- c )` is what a Forth programmer expects
to read. **This is a recurring bug source** — the old draft compared from the
head while appending residuals at the tail. State it at every boundary.

**D-06. Sums are primitive; products are stack segments.** A segment *is* the
product type; `TSeal` gives it identity. Sums cannot be segments because a
stack's shape is static and a sum's shape varies per branch.

**D-07. Code is first-class; functions are not.** A `{}` block is either
executed directly or consumed by a macro. No runtime closure values. Runtime
code exists only as the output of `specialize`.

**D-08. Linearity is opt-in via capabilities.** `Copy` licenses `dup`, `Drop`
licenses `pop`; a type with neither is linear. `Clone` is an ordinary interface
word, not a capability — as in Rust.
*Why:* the stack gives affine slot use, but `dup` and `pop` exist, so linearity
is not automatic. This is also what makes a `delete` word mean something a `pop`
does not.

**D-09. Two-tier Dictionary; static tier fully erased.** Static resolution
happens at elaboration and must cost nothing at runtime (M11 E3). Dynamic tier
is explicitly marked and compiles to handler-frame lookup.

**D-10. Modules are Dictionary handlers.** `use` pushes a static frame.
*Why:* one name-resolution mechanism, and module-level reinterpretation (swap
`math` for a SIMD `math`) is free.

---

## Syntax

**D-11. Named parameters live in the signature**: `( $x:f64 $y:f64 -- f64 )`.
Outputs stay positional types.

**D-12. Named parameters must occupy the topmost contiguous run.** A suffix in
surface notation. *Why:* binding pops from the top, so a suffix is a straight run
of pops; naming a buried parameter needs shuffles out and back, generating
exactly the hidden stack traffic locals exist to remove.

**D-13. Binding consumes.** Repeated reads are moves unless the type is `Copy`.
*Why:* a by-copy reading would require `Copy` on every bound type and be useless
for linear resources — the case where hiding stack juggling helps most.

**D-14. `let ($a $b) = { … }` destructures with `$b` on top**, mirroring
signature order.

**D-15. Brackets are self-delimiting.** `{hypot dup *}` and `{ hypot dup * }`
lex identically. Unlike Forth, no surrounding spaces required.

**D-16. No `;`.** `{}` delimits. No terse Forth names (`@`, `."`); `dup`, `swap`,
`pop`, `rot` stay.

---

## Rejected

**D-17. No implicit coercion.** The idea was coercing *functions* to match values
— given `hypot` at `f64` and arguments at `f64x4`, lift the function. Rejected
because that is **instance selection**, which is a search: the checker must
consider candidate liftings and choose.
*Not rejected for speed* — a value-coercion table is O(1) per slot and would have
been fine. Reinterpretation is written explicitly: `with simd_f64x4 {hypot dup *}`.

**D-18. No Pulse; extract to OCaml.** A compiler middle-end is a pure
tree-to-tree transformation, so Pulse's separation logic goes unused. Bootstrap
compiler performance is irrelevant — it runs once. No trust gain either; Karamel
and the OCaml extractor are both unverified paths.
*Revisit for P05/runtime*: allocator, concurrency, and JIT code buffers (mmap,
W^X) are genuinely imperative and Pulse would pay there.

---

## Implementation

**D-19. F\* is the source of truth.** Compiler passes are F* functions over
`M05_Terms.term`, extracted to OCaml for stage 0 and emitted as catcat source
for self-hosting. Self-hosting is a consequence of extraction, not a second
implementation.

**D-20. P02 stays in a first-order subset.** No closures, no higher-order
functions, no function-typed record fields. *Why:* catcat has no runtime
function values, so continuations must be data. R02 is defunctionalised
accordingly — which also makes deep handlers easy, since "the rest of the
computation" becomes a value in scope.

**D-21. Runtime values are type-erased.** P01's `vstack` is indexed by shape,
which is ideal for proving and unrunnable. R04 bridges them.

**D-22. `.fsti` for P02, not for P01.** A definition *given* in an interface
stays transparent; one only `val`-declared becomes opaque. M07's `denote` needs
`infer env TNil` to reduce, so interfacing M06 breaks the build. Verified
empirically, not assumed.

---

## 2026-07-27 session

**D-23. Handler frames must be inlinable, AOT and at JIT time.** Core to the
language's performance story, not an optimization to add later. A handler frame
that survives to runtime in the static tier is a bug, not a slow path.
*Consequence:* the stack-to-SSA pass (D04 §7) has to see through handler
boundaries, and M10's obligation H2 — handling is a monad morphism — is what
licenses moving code across one. **H2 is therefore load-bearing for performance,
not just tidiness.** Prove it early.

**D-24. Type erasure is right for execution but wrong for debugging.**
`R04_Erasure` throws away exactly the information a debugger needs to
reinterpret a running program under different rules (D01's tracing/profiling
goal). *Not yet resolved.* Options: keep a side table from stack position to
static type, or make erasure a parameterised pass with a debug mode that
retains indices. Recorded here so the debugger work does not discover it late.
See N02.

**D-25. Recursive types via pointer indirection, Rust-named.** `Box[t]`
(owning, unique) and `Rc[t]` (shared, refcounted), plus `TName` — an explicitly
annotated incomplete type. Recursion is legal only *through a pointer*, exactly
as in Rust and C++.
*Why this works without an environment:* a pointer's capabilities do not depend
on its pointee, so `has_cap` never looks through `Box`/`Rc` and never reaches a
`TName`. `dtype` values stay finite trees, so no positivity or termination
problem. An environment is needed only to unfold a `TName`, which typechecking
`Box`-opening needs and the runtime does not.
*Nullability* falls out of sums: `Option[Box[t]]` is the nullable pointer, no
new machinery.
*Acknowledged inefficient* — every recursive node is a heap cell. Optimize later.

**D-28. ~~`--` is self-delimiting, like the brackets.~~ REVERTED — `--` is an
ordinary space-separated word.** Only `{ } ( ) [ ] :` are self-delimiting, as
D-15 originally had it.

*What happened.* Building the lexer showed `( i64--i64 )` lexing `i64--i64` as
one word, and the reflex was to widen D-15 to cover the arrow. That was the
wrong fix, for two reasons that only became visible once D-30 was stated:

- **It was the lexer's only lookahead.** Distinguishing `--` from `-3` and from
  `pop-all` needs a *second* character. Every other decision in the scanner is
  a predicate on the one character in hand, so this one exception cost the
  DFA property for a single piece of punctuation.
- **It was the inconsistency, not the fix for one.** Everything else inside a
  `( … )` is space-separated. The arrow being an exception is the surprise;
  requiring the space removes it.

*Now:* write `( i64 -- i64 )`. `( i64--i64 )` is a single word and an error,
with a message that says so. `--` is therefore not available as a user word
name — the one cost, and a trivial one.

*Generalisable:* the first fix for a lexing surprise is usually to add a special
case. Check whether the surprise is the special case you already added.

**D-29. `pick` and `roll` added to the core.** `SPick above d` copies from
depth `|above|`, `SRoll above d` moves from it.
*Why:* `dup`/`pop`/`swap` reach only the top two slots, and **no composition of
them can touch a third** — so `$x` locals, which compile to n-deep access, were
unimplementable without this. Each carries the segment above the target rather
than a count, which keeps the rule non-variadic and the depth visible in the
type. `pick` copies and so is gated on `Copy` exactly like `dup`; `roll` only
moves and needs no capability.
*Elaboration strategy:* occurrence count decides — one read compiles to `roll`
(a move, nothing to clean up), two or more to repeated `pick` plus a drop at end
of body, zero to just the drop. Counting up front is what avoids a liveness
analysis.

**D-27. Sonnet delegation disabled; Haiku only, prompted raw.** Default is to do
the work directly. Haiku is permitted for short, mechanical, concurrent,
self-contained tasks. Never spawn Opus.

*Why:* the first real delegation run cost roughly 1.5–2× doing it directly
(~194k Sonnet tokens vs ~35k, cost-weighted for Sonnet's cheaper rate and the
fact that subagent spend is mostly input). It bought wall-clock time and nothing
else.

*The mechanism, which is the part worth remembering:* the orchestrator's context
is **prompt-cached at roughly a tenth of normal input cost**, so a file already
in context is nearly free to touch — while a cold subagent pays full price to
re-read it. The trial was the worst case: every file involved had been authored
minutes earlier. This gives a rule sharper than "parallelism vs overhead":

> **Delegate work whose input you do NOT already hold. Do work yourself whose
> input is already in your context.**

*Corollaries:* delegate reading (compresses — large input, small output), not
writing (expands, and the worker must load context first). Count workers, not
files — each pays ~15–20k orienting. Never write a long brief *and* let them
read; that is double payment and it is what happened.

*Two mental-model corrections:* subagents already start cold and never inherit
the conversation, so there is nothing to strip — "raw prompting" just means
keeping the brief minimal. And the crossover is **context novelty, not component
count**: many components already understood is still a bad trade, while a sweep
over unread code is a good one. The one case where delegation is an *enabler*
rather than an optimization is input exceeding the context window, where doing
it directly means compaction and lost fidelity.

*Not a capability judgment* — all three Sonnet workers produced correct work.
See the `delegate` skill for what would justify re-enabling it.

## Lexing, naming, inference

**D-30. No lookahead, in the lexer OR the parser.** The scanner is a plain DFA —
every branch is a predicate on the single character in hand — and the parser is
LL(1). A hard constraint on the grammar, not a property of the current
implementation.
*Why, in order of weight:*
1. **It is the precondition for a planned standard-library feature**: verified
   conversion of a left-recursion-free CFG into a recursive-descent parser. A
   language whose own grammar needed lookahead could not be described by the
   tool it ships. This is the reason that actually binds.
2. **Speed.** No buffer, no backtracking, no restart, so incremental reparsing
   for the language server is local.
*Consequence:* this is what decided D-28. Any future syntax proposal that needs
a second token to disambiguate is rejected on these grounds, not debated on
taste.

**D-31. Signatures are inferred; writing one is an assertion.**
`define sq { dup * }` yields `( i64 -- i64 )`. `define sq ( i64 -- i64 ) { … }`
still works and is checked against the body.
*Why it is nearly free:* concatenative composition **is** signature composition
(M03), so inference is one left-to-right walk — no constraint graph, no
generalisation, no Hindley–Milner. Model the stack; when the model runs dry the
body must be consuming another input, so invent a variable. Every word's
signature is ground, so the only constraint form is `variable := concrete type`:
flat map, no unifier, no occurs check, no union-find.
*Implementation (E04):* **two passes.** Pass 1 computes types and emits nothing;
pass 2 is the existing concrete elaborator, re-run with the inferred inputs in
hand. The alternative — emitting terms over unresolved variables and
substituting after — needs a second near-duplicate term type. Running a tested
pass twice over a definition body is cheaper in code and in risk.
*Limits, and why they are correct:* `{ dup }` is rejected because nothing
constrains the type. That is not an inference failure — the core is monomorphic
(D02 §5), so there is no signature to infer. Generics are what change this.
*Mandatory where inference is meaningless:* inside an effect declaration. An
interface fixes signatures before any implementation exists, so there is nothing
to infer from. Unenforced until effect syntax exists.
*This feeds the tooling goal.* The checker computes every word's stack effect
whether or not it is written, so a language server can show it inline, never
stale. See N02 Q-11.

**D-32. Arithmetic and comparison words are operators**: `+ - * / %`, `< <= =`.
Not `add`, `mul`, `lt` — those were placeholders from before the lexer existed.
*Consistent with D-16*, which bans *unreadable* abbreviations like `@` and `."`;
`+` is the most widely understood name a word can have. Word names are any run
of non-space, non-bracket characters, so this needed no lexer change.
*Two edges:* `-` is a word while `-3` is a literal, since an integer needs a
digit after the sign. `!=` is unavailable because `!` opens an effect sigil;
write `= not`.

## Control flow

**D-33. Booleans branch through a sum coercion, not a new eliminator.** One
core term, `M05.TBoolSum : ( bool -- TSum [[]; []] )`, with `false = tag 0` and
`true = tag 1`. Surface `if` is that coercion followed by the existing `TCase`.
*Why:* `bool` is a primitive, so `TCase` cannot see it, and a separate `TIf`
would need its own copy of the branch-agreement rule that `infer_branches`
already implements. The coercion reuses that rule, so the core grew by one
constructor and gained no new typing logic. The tag order is stated in four
places (`M01.bool_variants`, `M05.TBoolSum`, `R02.step`, `E02.StCase`) because
a silent reversal would typecheck.

**D-34. `if { c } then { t } endif`, with the terminator mandatory.** `else` is
optional; `endif` is not.
*Why:* at every alternation point the parser then *consumes* a keyword — after
the `then` block the next token must be `else` or `endif` — so the grammar has
no ε-branch. The alternative, an optional trailing `else`, is LL(1) only if
`else` stops being a legal word name, because otherwise a user word named
`else` following an `if` is genuinely ambiguous. Requiring `endif` costs one
token and keeps D-32's free-form words: `then`, `else` and `endif` are ordinary
names everywhere outside this production.
*Note this is not a lookahead violation.* LL(1) permits dispatching on the
token in hand without consuming it, which `parse_ty` and `parse_inputs` already
do. What D-30 forbids is needing a *second* token, and nothing here does.

**D-40. Branches agree row-polymorphically, not by having equal signatures.**
`M03.srow_join` frames each branch by what the other demanded extra and
compares the results, so

```
dup 10 < if { } then { 1 - } endif        \ accepted: ( i64 -- i64 )
```

is well typed even though `then` is `( -- )` and the `else` arm is
`( i64 -- i64 )`. What is rejected is disagreement at the head — one branch
consuming a `bool` where the other consumes an `i64` — since `unify` fails
there.
*Why the earlier rule was wrong:* `M06.infer_branches` required each branch's
`pre` to equal its variant payload exactly. For a `bool` both payloads are
empty, so no branch could touch the stack at all. Found by building `if`; the
rule had never been exercised because nothing but a hand-written example ever
constructed a `TCase`.
*Why it is cheap:* `M03.unify` and `lemma_unify_disjoint` already existed and
are exactly this. There are no type variables, only prefix matching, so D-31's
"no unifier anywhere" claim survives intact. `lemma_unify_common`,
`lemma_unify_refl` and `lemma_srow_join_sym` are proved, not admitted; the
order-independence of the fold across more than two branches is stated as an
obligation in M03 and wants discharging with `lemma_compose_assoc`.

**D-41. A local read inside a branch is forced to count as a repeated read.**
`E02.count_var` bumps the count for any `$x` occurring under an `StCase`.
*Why:* the elaborator compiles a sole read to a `roll`, which consumes the
slot. A slot consumed in one branch and not the other leaves the branches with
different stacks, so `if { } then { $x } endif` would be rejected for a reason
having nothing to do with what was written. Forcing `pick` costs an
end-of-body drop and requires `Copy`, which is the honest requirement — a value
read under a condition cannot be statically known to be moved exactly once.

**D-35. A macro is an LL(1) grammar production plus a term transformer.** It
declares a fixed slot sequence — blocks, words, literal keywords — followed by
an alternation in which **every branch is keyed on a word that is consumed**.
Its input is syntax and its output is surface terms, spliced into the enclosing
sequence.
*Two constraints, both deliberate:* a macro has **no stack access**, since
nothing it does survives to runtime; and it **cannot consume the enclosing
`}`**, because slots are parsed by the same functions the block parser uses and
a closing brace belongs to the block.
*Why every branch is keyed:* an unkeyed or optional tail is exactly what would
need a second token to disambiguate (D-30). The slot vocabulary cannot express
one, so `ll1_ok` — no two macros sharing a leading word, no two alternatives of
one macro sharing a key — is the whole LL(1) obligation, and it is *checked*
over the table by `assert_norm` rather than asserted in prose. This is the seed
of the planned verified CFG-to-recursive-descent generator: the same property
that tool must establish, established here on the grammar the language ships.
*Expanders dispatch on the macro name rather than sitting in the record as a
field* — a function-typed field would break the first-order subset (D-20), so
the dispatch is defunctionalised exactly as R02 defunctionalises continuations.
*Status:* the table is built in and `if` is its only entry. User-defined macros
are what it exists for and need the elaboration-time interpreter; the shape of
the table is fixed so that registering one later is registration, not redesign.

**D-42. `true` and `false` are prelude words, not literals.** Bound to
`WDef (bool_lit _)` in `R03_Prelude`.
*Why:* making them words costs nothing, since specialization inlines a `WDef`
whose body is a literal, and it buys two things — they shadow like any other
name, and neither the lexer nor `E04` grows a case. Until now there was no way
to write a `bool` at all, so `and`/`or`/`not` were reachable only through a
comparison.

## Effects and handlers

**D-36. A handler never captures a continuation. It is a stateful object.**
An operation call runs an implementation, which RETURNS. `M05.THandle` carries
a state segment and an initialiser; the state is threaded through each
implementation's own signature, types preserved. A stateful handler is
therefore literally D03 §3's `class … over ( … )` — D-01 confirmed a third
time, and one construct fewer than a separate class feature would need.
*Why:* continuations must not be a runtime construct in the compiled language.
Everything a resume-exactly-once handler can do is expressible by returning,
and the object model is what the design already wanted for classes.
*Reentrancy does not need capture.* `R02.step` runs an implementation with the
`KHandler` frame still installed, so operations the implementation itself
performs reach the same handler. That is the whole of "every effect is
reentrant" (D03 §2) and it costs nothing.
*Consequences:* `M06.infer_impls` types an implementation as an ordinary
program; N02 Q-02 closes by decision, since no handler holds a continuation and
there is nothing extra to type; and D03 §2's paragraph about running the
continuation "zero, once, or many times" is wrong and gets rewritten.
*What is given up:* nondeterminism where one choice makes the rest of the
enclosing program run more than once. A free-list-monad effect is still
available with the multiplicity **reified as a value** — an operation returning
a list, or one whose alternatives are delimited blocks the handler schedules.
That is the form that survives compilation to a state machine.

**D-46. Handler state sits on TOP of the operation's arguments.** An
implementation of `o` is typed at `{ pre = st @ o.op_pre; post = st @ o.op_post }`,
so in surface order it reads `( args… state -- results… state )`.
*Why:* not a preference. The reference machine splices the state in at the
moment of the call, and the dictionary records only which effect an operation
belongs to, not its arity — so the top is the only position reachable without
adding arity to `R01.rword`. It reads correctly anyway: the state is the
receiver, and a receiver is pushed last, so `counter tick` is the natural
spelling. A stateless handler is `st = []` and needs no separate rule.

**D-47. On exit, a handler leaves its final state on the stack.**
`THandle`'s signature is `{ pre = body.pre; post = st @ body.post }`.
*Why:* the handler is the object, so the object outlives the block. Discarding
the state instead would require `CDrop` and would silently throw away the
result of whatever the state was accumulating — which for a counter or a log is
the entire point of having run it.

**D-48. Re-entering a handler while its own state is lent out is an error.**
`R02` blanks the frame's state for the duration of an implementation, and an
operation reaching that frame meanwhile gets
`STUCK: handler re-entered while its own state is in use`.
*Why:* the alternative is serving a stale copy, which silently forks the state.
This is the aliasing rule a linear language ought to enforce statically — it is
`RefCell`'s dynamic borrow check, with the same justification and the same
admission that a static version would be better. Recorded as an open question
rather than pretended away.

**D-49. The host is the outermost handler, and `IO` is effect 0.**
`print` and `read` are ordinary operations of an ordinary effect. What makes
them the compiler's to supply and not the user's is that the interpreter owns
effect id 0 while the surface `effect` declaration allocates from 1 upward, so
an `IO` operation can never find a handler inside the program and always
escapes to `R05`'s caller.
*Why:* category 2 of the effect design needed no new language feature at all —
only the observation that a pure `run` reaching an unhandled operation can hand
its caller what it needs to carry on. `bin/catcat.ml` performs the operation and
calls `resume`.
*The `kont` this exposes is NOT a language-level continuation.* No catcat
program can name it, no `dtype` describes it, no handler sees one, and D-36 is
untouched. It is the interpreter's own machine state, exposed because a pure F*
function cannot perform IO. A compiled program calls the runtime directly and
has no such object — stated as an obligation in `R05_Driver.fsti`, because the
place it could quietly stop being true is a backend that implements built-in
effects by copying this driver's shape.

**D-38. `effect` and `handle` are parser built-ins, not macros.** They need
sub-grammars — a block of `op { … }` pairs is not a term list — and the macro
slot vocabulary should not be stretched to cover them before it has been
exercised on the constructs it already fits.

**D-39. Coroutines and generators come from staging into a state machine**,
never from a runtime continuation. Resume points are reified as data at
elaboration time; resuming is a call that switches on that state, the strategy
Rust uses for `async`.
*Why:* it keeps D02 §6 (no runtime function values) intact and puts control
flow under `specialize`, where D04 already puts everything else staged. It is
also why this work waits on the static-`with` substitution pass — attempting it
first would mean building that pass twice.

## Inspection

**D-43. `locate` decompiles the core term; no source text is retained.**
`E05_Locate.show_items` renders a `M05.term` back into surface syntax, using
the session's name environment to turn `word_id`s back into names.
*Why:* keeping the source text alongside the definition means keeping two
things in agreement, and every pass that rewrites a term — macro expansion
today, `specialize` from M6 on — would have to maintain the copy. A term cannot
go stale relative to itself. The second reason is the one that decided it:
because the output is surface syntax that **re-parses to the same term**,
`locate` is a test of the elaborator rather than a convenience. Verified by
feeding `locate abs`'s output back in, including nested `if`.
*Consequence:* where the surface language cannot spell a core construct, the
rendering is deliberately **not** valid syntax — `pick.2`, `#7` for a word with
no name in scope — rather than a plausible-looking lie. Deep stack access is
the standing case: `$x` locals are gone by then and their names with them.

**D-44. `locate` is a declaration, recognised by position, not a word.**
Like `define`, `locate` is matched at the start of a declaration and nothing
reserves the name — `define locate { 42 }` is still legal, and `locate` inside
a body is an ordinary word.
*Why:* its argument is a NAME, not a value. It has nothing to do with the stack
and therefore has no signature to give it, so it cannot be a word in a
statically stack-typed language. Forth reaches the same shape from the other
direction by making `LOCATE` immediate; here the position rule does it without
needing immediacy to exist yet.

## The specification's own representation

**D-45. No function-typed record fields anywhere, including P01.**
`M04.sig_env` and `M06.wenv` are association lists with total lookup functions
(`op_of`, `eff_of`, `w_sig`, `w_eff`); an unknown id resolves to a declared
default rather than failing.
*Why:* the first-order subset (D-20) was stated as a rule for P02 because P02
extracts to catcat. But P03 must CONSTRUCT a `wenv` to call `infer`, and
constructing a function-typed field needs a closure — so the rule was being
violated in the one place that could not avoid it, and would be violated again
by anything that ever wants to build a specification environment. Making the
spec's own environments first-order costs nothing: `op_of` is still a function,
just a defined one rather than a field.
*Totality is load-bearing:* `M04.op_of` appears inside the TYPE of `free`, so
it cannot return an option. The default is the nullary operation of effect 0,
and it is safe because M06 checks an operation is declared before accepting a
program that uses it — the default is never what a well-typed program sees.
*What this actually unblocked:* `E06_Repl.mk_wenv` had been faking the
operation table with closures returning junk, because there was no honest way
to build one. Handler typechecking reads exactly that table (`M06.infer_impls`),
so the fake would have accepted every handler implementation without complaint.
This is why it is a prerequisite for the effect system and not a cleanup.

---

**D-26. Wrapping unsafe primitives into the linear system is a recurring
theme.** `Box` and `Rc` are the first instance and will not be the last; expect
the same for file handles, sockets, mmap'd buffers, GPU allocations.
*The pattern:* the unsafe thing gets **neither `Copy` nor `Drop`**, making it
linear, and its safe operations become **interface words** — `clone` on `Rc`
increments a count, `release` decrements, and neither is a bitwise copy or a
no-op discard.
*This is a strong confirmation of D-08*: capabilities-plus-`Clone`-as-interface
is exactly the shape `Box`/`Rc` need, and it was chosen before they existed.
When adding any future resource type, start from this pattern.
