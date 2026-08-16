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

**D-31. Signatures are inferred; writing one is an assertion.** — the surface rule is superseded by **D-77** (three modes, and a bare `!` for an asserted-empty row); the inference argument below stands, and D-77 extends it to generics.
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
core term, `M05.PBoolSum : ( bool -- TSum [[]; []] )`, with `false = tag 0` and
`true = tag 1`. Surface `if` is that coercion followed by the existing `TCase`.
*Why:* `bool` is a primitive, so `TCase` cannot see it, and a separate `TIf`
would need its own copy of the branch-agreement rule that `infer_branches`
already implements. The coercion reuses that rule, so the core grew by one
constructor and gained no new typing logic. The tag order is stated in four
places (`M01.bool_variants`, `M05.PBoolSum`, `R02.step`, `E02.StCase`) because
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
*Expanders were originally dispatched on the macro name* because a
function-typed field would break the first-order subset (D-20). They are now a
**template**, which is data, so the dispatch is gone; `if` alone is still
name-dispatched and carries `mp_builtin = true` to say so, because its expansion
is a `case` and `case` has no surface spelling.
*Status:* user-definable — see D-53.

**D-53. A macro's expansion is a TEMPLATE, and templates are expanded at
declaration time.** `macro name ( slots ) { template }`, with `{ $x }` for a
block slot, `$x` for a word slot, and a bare word for a consumed keyword; keyed
alternatives are `alt key ( slots ) { template } … end`. Substituting a block
slot **splices**, so `{ $b $b }` with `$b = 1 +` gives `1 + 1 +`.
*Why a template rather than a program:* the user's eventual target is a macro
that is an ordinary word with an effect letting it consume and transform code,
which needs an elaboration-time interpreter. A template is the subset of that
which needs nothing: it is data, so no function-typed field appears, and it is
enough to define every macro the language currently wants.
*The termination argument is the declaration order, not a check.* A macro's
template is parsed against the table **as it stands**, so it may use macros
declared before it — already expanded by the time it is registered — and cannot
use itself. Expansion therefore cannot loop, and no fuel or occurs check is
needed. This property is worth preserving when macros become programs.
*Nothing is hygienic, and that is stated rather than hidden.* A `$x` in a
template naming no slot is an ordinary local read, resolved in whatever encloses
the expansion. Hygiene is a real question and is deferred, not solved.
*The LL(1) invariant now holds dynamically.* `ll1_extend` decides `ll1_ok` before
accepting a production and `lemma_ll1_extend` states that every table a session
parses against therefore satisfies it. `assert_norm` still covers the built-in
table, but the interesting check moved to run time because the grammar did.

**D-54. Parsing and evaluation interleave, one declaration at a time.**
`eval_line` lexes the whole line, then repeatedly parses ONE declaration against
the session's current grammar and runs it.
*Why:* a `macro` declaration changes the grammar the rest of the input is read
with, so the old shape — parse the whole line, then evaluate the list — could
never let a macro take effect where it was written. Forth's `IMMEDIATE` has the
same shape for the same reason.
*What it costs, said plainly:* "a parse or type error leaves the session
untouched" was a documented property and is now only true of LEXING errors. A
line that half-parses leaves the declarations before the error applied. In a
REPL where a line is one thought this is nearly never observable, and it is the
honest price of macros being part of the language rather than of the compiler.

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

**D-37. `!Dict` is to effect rows what the implicit row variable is to stack
signatures** (D-04). Pervasive, never written, static by default, and made
explicit only when a program wants to talk about it.
*Why:* a word's meaning always depends on the dictionary it was elaborated
against — that is what an interpreter is doing statefully, and `!Dict` is the
direct encoding of it. Rows nonetheless stay clean, because a statically
resolved word is `TWord w` in the core, not a `Dict` operation: the implicitness
is a surface and elaboration notion, and `M04.within` never sees it.
*Consequence, and it is the load-bearing one:* static `with` needs no row entry
at all. A rebinding that is discharged at elaboration leaves no trace, which is
M11's E3 — a fully static effect costs nothing — holding by construction rather
than by theorem.
*Not yet implemented:* the dynamic opt-in, which would add a real `!Dict` entry
to the row and consult the handler chain on `TWord` at runtime.

**D-50. Static `with` is word-id substitution over the elaborated term, and it
is the first running piece of D-02.** `with { old new … } { body }` elaborates
the body under the ORIGINAL names, then rewrites word ids with
`M05.subst_words`.
*Why elaborate under the original names:* the shape model stays the one the
reader wrote, and the substitution provably cannot disturb it, because the
rebinding is required to preserve the signature. The effect ROW may change
freely, and that is the point — rebinding `noisy` to a pure word makes the
enclosing definition pure, which is reinterpretation of a program by overriding
words.
*Why it matters beyond convenience:* this is `specialize` restricted to one
kind of static effect. `locate` on a definition that used `with` shows the
substituted words and no trace of the `with`, so E3 is demonstrated by running
the binary rather than assumed by a theorem that is still unproved.
*The signature check is the hypothesis of M11's E7*, enforced by the elaborator
because E7 is stated and not proved. It becomes redundant, not wrong, once it is.

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

**D-51. `M04.free`'s continuation is a restricted function (`^->`), and the
monad laws are proved via helpers applied to a literal `Op` node.**
*Why the type changed:* right identity and associativity are true pointwise,
but the two sides build syntactically different continuations, so `==` on a
plain arrow is unprovable. `FStar.FunctionalExtensionality`'s `^->` is the
library's device for exactly this, and it costs one `on` at the single site
that constructs an `Op`.
*Why that is not sufficient on its own, which is the part worth remembering:*
**two alpha-equivalent lambdas written at two different places are different
closures to the SMT solver.** An induction that spells out `fbind`'s
continuation at its own site can therefore never connect it to the one `fbind`
actually built, and no amount of `extensionality` will bridge the two. The fix
is to hand the `Op` step to a helper taking the constructor APPLIED — F* then
reduces `fbind` by conversion, and the continuation is obtained by PROJECTION
rather than written down, so a second closure never exists. Associativity's
composite is passed as a parameter for the same reason.
*Where this bites next:* M10's H2 and H3 need the same manoeuvre, and cannot
use it as-is, because `handle`'s `Op` case is guarded by `eff_of env op = eff`
and conversion cannot decide that test. They want an `Op` congruence over
projected continuations, which needs a projection to typecheck against a
propositional equation rather than a definitional one. Recorded so the next
attempt does not rediscover the closure problem from scratch.

**D-52. `stage_required` answers only `ReqNone` / `ReqSpecial`, and says so.**
The other two constructors describe stages nothing in `M05.term` can yet
demand: `ReqCodegen` means the residual must be emitted as machine code rather
than interpreted, which is a property of the host and not of the program, and
`ReqFull` needs a term that consumes source text, of which there is none.
*Why define it at all rather than leave it assumed:* the two answers it does
give are the ones a linker consumes, and they are decided outright by
`M05.needs_compiler`. An `assume val` here was claiming a distinction the core
cannot make; a definition plus a paragraph naming what it cannot decide is the
honest form of the same content. Same principle as the `DOCS/` hygiene rule —
a cache that says what it does not know beats one that quietly guesses.

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

---

**D-55. The core has seven term constructors; every intrinsic is a table row.**
`M05.term` was nineteen constructors, twelve of which were the same thing: a
primitive whose signature is a function of its own arguments and whose meaning
is a pure stack transformer. Those twelve become one constructor `TPrimOp` over
a flat `prim_op` table. What remains is the language's *structure* — `TNil`,
`TSeq`, `TPrimOp`, `TWord`, `TCase`, `THandle`, `TSpecialize` — and nothing else.

*Why:* each intrinsic needs a signature (`M06.prim_sig`), a denotation (M07) and
a machine action (`R02.apply_primop`). As constructors, adding one meant
amending three functions and growing every induction over `term` in M07 and M09
by a case. As a table, adding one is a row and each induction has a single
uniform primitive case discharged once. `TRcDrop` is a refcount protocol, not a
feature of a stack calculus, and it had no business sitting beside `TSeq`.

*The invariant that pays for the grouping:* **every primitive is pure.**
`prim_sig` returns no effect row, and `apply_primop : prim_op -> rstack ->
either string rstack` is given neither the dictionary nor the continuation, so a
primitive cannot perform an operation, call a word, or alter control flow —
because it is handed nothing with which to do so. M07's T4 therefore covers the
whole class at once. Anything that could perform an effect is a `TWord`
resolving to an operation instead, which is why `print` is not in the table.

*Timing:* done before `denote` and `step` were written, deliberately. Either
would otherwise have been twelve clauses that were then deleted.

*Cost:* `R01`'s `prim_op` — the reference interpreter's built-in words `+`, `-`,
`not` — was renamed `prim_word`, which it more accurately was: those are
dictionary entries, not core terms. The two lived in the same scope in R02.

---

**D-56. Native types come from F* libraries, not from the core.** `Box` and `Rc`
are in `dtype` and `prim_op` today because they were needed before there was a
facility to add them from outside. The facility, when built, lets a library
written in F* contribute a type together with its operations, their signatures,
their denotations and the **invariants it proves about them** — so `Rc`'s
refcount discipline becomes a library theorem rather than a core axiom.

*Why this is the same construct as everything else (D-01 again):* such a library
contributes exactly what a `prim_op` row contributes — signature, denotation,
machine action — plus a proof. So `prim_op` becomes the *built-in* half of a
two-level table and `Box`/`Rc` move out of it into the first client library.
That is a change of lookup, not a change of language, which is why `prim_op` is
shaped as a flat table now rather than as ad-hoc constructors (D-55).

*What has to be decided before building it:* the boundary. A native entry can be
trusted (its denotation is axiomatic, like a syscall) or proved (its denotation
is an F* function and the invariants are theorems). Both are wanted, and they
are not the same obligation — a trusted entry enlarges the TCB and must say so.
`IO` is probably the motivating trusted case, and it would then stop being an
interpreter special case (`R05_Driver`'s host handler) and become a library.

*Not implemented. Recorded so that D-55's shape is not mistaken for an accident.*

---

**D-57. `unsafe` is an effect with no operations, discharged by `with unsafe`.**
An effect need not declare any operations. `M06.infer`'s `TWord` rule takes the
row straight from the declaration, so a word can carry `!Unsafe` without there
being an operation of that effect to perform; `THandle` with an empty
implementation list discharges it. **An effect with zero operations is a
permission, and the row machinery already supports it** — nothing new is needed,
not even a placeholder no-op operation.

*Why this beats a keyword:* Rust needs both `unsafe fn` and `unsafe { }` and a
lint to connect them. Here a word that leaves `!Unsafe` in its row *is* an
unsafe function, by the same rule that makes a word that leaves `!IO` in its row
an IO function — the propagation is the effect system doing its ordinary job,
and a word cannot hide its unsafety by forgetting to annotate. `with unsafe { …
}` is then an ordinary handler, every use is greppable, and there is no
questionable behaviour to compare against Rust because there is no special case.

*Vocabulary note, since it was asked:* the members of an effect are
**operations** (`M04.op_id` / `op_decl`, surface `declare`). Not slots, not
methods. `Unsafe` has none.

*Open:* whether the elaborator should refuse `with unsafe` around a body whose
row does not contain `!Unsafe`. Warning, not error, most likely — the same
question Rust answers with `unused_unsafe`.

---

**D-58. Macro determinism and termination get stated in F*, not argued in
prose.** Both follow from the shapes already in `E03_Parser` — `expand` is a
total function, and a template is parsed against the macro table *as it stood*,
so a macro cannot reference itself. Neither is hard. But "it follows obviously
from the code" is exactly the kind of claim that stops being true after a
refactor nobody re-read the argument for, and the whole point of a mechanized
core is that load-bearing properties are checked rather than believed.

*What this is NOT:* soundness. A macro's output is surface syntax, which
elaboration re-checks with `M06.infer`, so a buggy macro produces a type error
and never an ill-typed program. Macros stay out of P01 entirely for that reason
— the sense in which they need to be correct is weaker than soundness and lives
in P03, where the parser is.

*The three properties, and where each stands:*
1. **Deterministic parsing.** `ll1_ok` decides it and `ll1_extend` maintains it
   (`lemma_ll1_extend`). What is still missing is that `ll1_ok mt` implies the
   parser never needs to backtrack — that is the theorem the planned verified
   CFG-to-recursive-descent generator (D-30) owes.
2. **Terminating expansion.** Structural, by declaration order.
3. **Hygiene.** Absent, and the one genuinely unresolved item (D-53).

---

**D-59. The handler fold lives with the free monad, not with the handler
narrative.** `op_impl`, `handler`, `handle`, `id_handler` and the new `fwd_impl`
moved from `M10_Handlers` to `M04_Effects`. M10 keeps `dict`, `resolvable`, the
five obligations H1–H5, and the argument that one record is simultaneously an
effect handler, a typeclass dictionary, a class method table, a module
implementation and a Dictionary frame.

*Forced by:* `M07.denote_static`'s `THandle` clause is a call to `handle`.
Leaving the fold in M10 would have made M07 depend on M10 and broken the rule
that numbering and dependency order coincide — a rule the skeleton was already
quietly bending, since M07's T5 and M09's `state_typed` both said "depends on
M10".

*Why the seam is right and not merely convenient:* `handle` is the eliminator of
`M04.free` and needs nothing but the monad — no `srow`, no `wenv`, no typing
judgment. What genuinely needs M06 is H1, which relates `handle` to
`row_remove`, and that stayed. Mechanism with its type; meaning where the
judgment is. M10's header now lists what moved, so its shortness is not read as
emptiness.

---

**D-60. A word call and an operation call are the same node of the free monad.**
`M07.denote_static` gives `TWord w` the denotation `Op w arg k`. There is no
alternative: `M06.wenv` records a word's signature and effect row, never its
body, because which body it has is exactly what the ambient Dictionary decides
(D-37). So a word is an operation, and `M04.handle` against the Dictionary frame
is what supplies its meaning — at elaboration time in `M11.specialize`, at
runtime in `R02.find_handler`.

*This is D-01 arriving somewhere it can be checked.* It also collapses a large
part of `specialize`: inlining a statically resolved word is not a special case
of partial evaluation, it is `handle` run early.

*Two consequences, both real, both recorded rather than hidden:*
1. **`wenv`'s two tables must agree.** `M04.Op` demands arguments of shape
   `(op_of w).op_pre` while the signature supplies `(w_sig w).pre`. Nothing in
   M06 related the two tables and nothing had to until now. `M07.coherent` is
   that condition. It holds vacuously for words in neither table, so it
   constrains exactly what it should — but **P03 does not currently satisfy it**:
   `E06_Repl` registers an `effect`'s operations in both tables and a plain
   `define` in only one. See N02 Q-14.
2. **M07's T5 was false as stated.** A word with an empty row performs an
   operation, so `within row (denote t)` fails on the simplest possible program.
   `!Dict` has to stop being an elided convention. Also N02 Q-14; the fix closes
   both at once, which is why they are one question.

---

**D-61. `denote_static` is the denotation of `not (needs_compiler t)`, and T2 is
a combinator rather than a theorem.**

*The fragment.* Six of the seven core constructors; `TSpecialize` is excluded.
That predicate is not invented for this purpose — `M11.stage_required` already
uses it to decide whether a binary needs a compiler linked in at all, and
`TSpecialize`'s meaning is M11's E2, which is stated against `denote_static`. So
defining it here would be circular, and the fragment boundary is the same one the
linker draws.

*The signature.* `denote_static` TAKES the signature and effect row plus a
`squash` of the `infer` equation, rather than computing
`fst (Some?.v (infer env t))` in its own result type. This is the change that
made the definition possible at all, and it was the sticking point for several
sessions: with the index computed, every recursive call's type mentions an
unreduced `infer env a`, and the `TSeq` clause has no way to say the composite's
shape is built from the operands'. Taking them turns each clause's obligation
into ordinary equations between segments, which `append_assoc` and
`M03.lemma_unify_common` can discharge.

*T2 is discharged by construction.* `dcompose` — composition of denotations along
`M03.compose`, residuals and all — is the statement that juxtaposition denotes
Kleisli composition, and the `TSeq` clause is a call to it. There is no theorem
left. The same trick does not work for T3–T6, which are properties of the
definition rather than its shape.

*Non-vacuity is checked, not assumed.* A `cdenote` is a function, so a definition
full of transport can be well typed and still not reduce to an answer. M07 ends
with two worked examples discharged by conversion: `2 3`, which exercises `TSeq`
with a non-empty residual, and `7 true if { } then { pop 9 } endif`, which
exercises `PBoolSum`, `srow_join` between branches of unequal depth, and the
skipping path of `denote_case`. This is `make interp`'s job for the denotational
side and should grow the same way.

*What writing it found, none of which was visible from the typing rules:* D-60
above, T5's falsity, N02 Q-13's soundness hole in roll/unroll, and two missing
`M02` operations (`vpick`, `vroll_up`) whose absence would have put a duplication
outside the one file T6 quantifies over.

---

## D-62. A soundness hole is fenced by a precondition, never by an `admit`.

`M07.prim_den`'s `PUnroll` clause was `admit ()`, with a comment saying the case
has no denotation as `M06.prim_sig` types it (N02 Q-13). That comment was
accurate and the `admit` was still the wrong device.

*Why the distinction is not cosmetic.* An `admit` makes `denote_static` total by
fiat on a case whose semantics does not exist. Every theorem stated about the
function afterwards — T3, T4, T6 — is then quantified over terms containing that
case, so each is silently conditional on a fix nobody has made. Replacing it with
a precondition makes the same theorems UNCONDITIONAL statements about a
well-defined fragment, and the fragment grows when roll/unroll is settled.

So `M05.uses_unroll` joins `needs_compiler` as a syntactic predicate over terms,
`denote_static` requires both to be false, `prim_den` is refined by
`not (PUnroll? p)`, and the clause is `false_elim ()`. M07 now has no `admit`.

*They are not the same kind of exclusion, and the code says so.* `TSpecialize`
is a PERMANENT boundary — its meaning is M11's E2, which is stated against
`denote_static`, so defining it there would be circular. `uses_unroll` is a
DEFECT MARKER: it gets deleted rather than discharged, and it is deliberately not
folded into `needs_compiler`, which the linker consumes and which has every
reason to survive. Merging them would hide a defect inside a permanent feature.

*Generalisable rule:* when a case is unimplementable rather than merely unproved,
exclude it from the domain. An `admit` says "this is true and I have not shown
it"; the case here is not true.

---

## D-63. One signature table. `w_sig` reads from `w_ops`, and `!Dict` is effect 0.

D-60 established that a word call and an operation call are the same node of the
free monad. `M06.wenv` nevertheless carried TWO signature tables — `w_defs` for
words, `w_ops` for operations — with nothing relating them. M07 stated the
missing agreement as `coherent env` and refined `denote_static` by it.

*That was the wrong repair, and the failure mode is the interesting part.* P03
did not satisfy `coherent`: `E06_Repl` registered an `effect`'s operations in
both tables but a plain `define` in only one, and the prelude in only one. So the
denotation was vacuous for every program the REPL could actually elaborate — a
semantics for nothing, at exactly the point where the spec is supposed to mean
something. A side condition maintained by discipline in another directory is not
a fix; it is the drift written down.

*The fix is to delete the second copy.* `M06.w_sig` is now
`sig_of_op (op_of env.w_ops w)`. The two tables cannot disagree because there is
one of them, `coherent` is definitionally `True` and is gone from M07, and P03
cannot regress: a word absent from `w_ops` has no signature rather than a stale
one. `wenv`'s remaining field is `w_effs`, holding the one thing `w_ops` genuinely
does not know — the effects a word's BODY performs, which is not a property of
its declaration.

*The same change closes T5.* `M04.eff_dict = 0` is reserved for the Dictionary,
`op_decl` gains `od_stage`, and `M06.w_eff` DERIVES the head entry
`(eff_of w, stage_of w)` rather than trusting a stored one. So `TWord w`'s row
always mentions the effect its denotation performs, and T5 is true as originally
written with no `dict_row` prefix and no special case. `!Dict` stops being an
elided convention and becomes an ordinary effect that happens to be reserved.

*Consequences taken.* `R03.eff_io` moves 0 → 1 and user effects allocate from 2;
`bin/catcat.ml` dispatches on the WORD id, so the host loop is untouched.
`M04.op_unknown` now defaults to `Dict`, which is what an unbound word actually
is — before, it silently claimed `IO`. `M06.row_visible` elides a STATIC `Dict`
entry, and `E05.row_effs` is the single place that happens, so rendering and the
REPL's declared-effects check agree by construction. A dynamic `Dict` entry is
not elided, because that one is a real claim.

*Accepted cost:* nothing that calls a word is `is_pure` any more. That is not a
regression but D-37 being honest — and it is precisely the property M11's E3
claims `specialize` restores, so the statement got sharper rather than weaker.

---

## D-64. An obligation is a type; discharging it is exhibiting a value.

A proved law was a scatter of separate lemmas plus a comment saying what they add
up to, and an unproved obligation was prose. Both are mechanized now, by the same
device and for two different reasons.

*Proved laws become records.* `M02.frame_is_functorial`,
`M03.srow_is_partial_monoid` and `M04.free_is_monad` are values whose fields are
the existing lemmas — no new proof, no new obligation, and the classification is
now checked instead of asserted. The gain is that nothing can quietly stop adding
up: restate one lemma and the bundle fails to build.

*Unproved obligations become uninhabited types.* `M07.t3_type`, `t4_type`,
`t5_type` are the statements; the absence of a value is the gap. `t1_type` and
`t2_type` are inhabited by `thm_t1` and `thm_t2`, both `()` — which turns "T2 is
discharged by construction" from a claim into a proof of the equation it was
claiming.

*Records, not `class`es, for now.* In F* a class is a record plus tactic-driven
instance resolution. The bundling is what is wanted; resolution pays only when a
later module wants to be generic over "any lawful X", and today each structure
has exactly one. Promoting is one keyword when P04 needs it, so nothing is
foreclosed by starting concrete.

*NOT in M01, and this is the one place the natural instinct is wrong.* M01 knows
`dtype`, `seg` and `cap`. A law bundle whose fields mention `frame`, `compose`,
`fbind` or `denote_static` cannot precede those functions, so hoisting the
declarations to M01 would need them carrier-polymorphic — and the carriers here
are all bespoke (`free` is a RELATIVE monad along `vstack`, not an
`m:Type -> Type`). That would be abstraction written for one inhabitant, at the
cost of the invariant that numbering is dependency order. Each bundle therefore
sits at the foot of the module that owns its structure.

*And explicitly NOT `assume val`.* An `assume val` of an obligation makes it
available to later proofs. T5 was FALSE for three commits; assuming it would have
made the development inconsistent rather than merely incomplete. A bare type is
the safe half — checked as a statement, useless as a hypothesis, which is exactly
right for something unproved. This is the same principle as the ban on
`Lemma True`, applied to a mechanism that would otherwise look more respectable.

*What is not covered.* M08's O-series, M09's S-series and M11's E-series are
statable as types but mention `step`, `run`, `state_typed` and `specialize`,
which are `assume val` — so no value could be exhibited until those are defined,
and the types would be documentation with extra syntax. M07's T6 cannot be stated
at all: it needs an erasure from `vstack` to a multiset of leaf values and M02 has
no such function. Saying so is better than a type that approximates it.

---

## D-65. `str` is a primitive; IO moves strings, not numbers.

Two changes, one of which forced the other.

*The type.* `M01.prim` gains `PStr`, with `prim_rep PStr = string`. A TABLE ROW
AND NOT A `dtype` CONSTRUCTOR, which is the same choice D-55 made for
intrinsics: a constructor would touch `dtype_size`, `has_cap`, `wf_dtype`,
`R04.erase_value` and every renderer, whereas a row touches `prim_rep` and the
handful of places that enumerate primitives because they must. It is abstract in
the sense `f32` already is — the core never inspects a string, since
concatenation and formatting are `R01.prim_word` entries rather than core
operations, so an F* `string` is enough for everything M02–M11 says.

*IO.* `print` and `read` were `( i64 -- !IO )` and `( -- i64 !IO )`. They were a
placeholder from before there was a string type, and an IO facility that can
only move integers cannot emit a message. They are now `str`-typed, and `print`
adds NO newline — the string is written as itself, which the `i64` version had
no room to offer.

*Four prelude words came with it, and three of them are not optional.* `show`
(`i64 -- str`) and `parse` (`str -- i64`) exist because string IO must not COST
the numeric IO it replaces; without them a number can neither be printed nor
read. `cat` is the third, because a message is a literal and a value joined, and
without it the only printable strings are the ones written whole. `str=` is the
one convenience — spelled separately from `=` because the core is monomorphic
(D02 §5) and a single `=` over both types is an interface, which is D03's job
and not something to fake with a second prelude entry.

*Lexing stays a DFA (D-30).* A double-quoted literal needs two states —
in-string and after-backslash — and every decision remains a predicate on the
one character in hand. NEWLINES ARE ORDINARY CONTENT, as in Perl, so a literal
spans lines with no heredoc and no continuation character; the cost is that an
unclosed quote is reported at end of input rather than end of line, which is the
trade the `{` … `}` rule already makes. Escapes are `\n \t \r \" \\` and an
unrecognised one is an ERROR rather than the character itself, because `"\q"` is
a typo far more often than an intent.

*Two acknowledged rough edges, both recorded rather than papered over.*
`E05.show_lit` re-quotes a decompiled string without re-escaping it, so `locate`
on a word containing `"\n"` prints text that will not re-parse — the fix is to
invert `E01.escape_char`, and it belongs with escaping on both sides rather than
as a patch on one. And `parse` yields 0 on malformed input, exactly as the
`i64`-typed `read` already did; the honest type is `( str -- option[i64] )` and
it becomes writable when sums have surface syntax.

---

## D-66. Four reserved effects, and `extern` is `declare` at effect `C`.

The host effects are now a block rather than a special case: `0 Dict`,
`1 IO`, `2 Unsafe`, `3 C`, with `R03.eff_user_base = 4`. A surface `effect`
allocates from there and so cannot name one, which is the entire mechanism — a
fact about who owns the identifier, not a restriction the effect system had to
grow. `se_next_eff` used to be a literal `2` in P03 that a fifth reserved effect
would have silently invalidated; it reads `eff_user_base` now.

**Reserved does not mean unhandleable**, and that distinction is the payoff.
`handle IO … { print { pop } }` mocks output, and `handle C … { strlen { pop 99 } }`
mocks a foreign call — the same construct, reached the same way. Being able to
stub libc for a test without a test double, a linker flag or a build variant is
the most practically valuable thing D-01 has produced so far.

*`Unsafe` needed no code at all, which was the D-57 prediction and it held.* It
has no operations. A word carries `!Unsafe` in its row without there being
anything to perform, unsafety propagates by the ordinary row rules, and
`handle Unsafe over ( ) init { } { } { … }` discharges it. The surface `unsafe
{ … }` is a MACRO — spelled out in `E03.builtin_macros` in exactly the form a
user would type, and `locate unsafe` prints it. So there is no keyword, no
elaborator case, and no lint connecting a declaration to a block, where Rust
needs all three.

*`extern name ( sig )` is `declare` at a different effect.* Same parse shape,
same mandatory signature and for the same reason (D-31: no body to infer from).
The word name IS the C symbol; an aliasing form would need a second name in the
syntax to buy what `with { strlen len }` already does.

*Every `extern` word carries `!C` AND `!Unsafe`*, and that is D-63's split
paying off rather than a special case. `M06.w_eff` returns the DERIVED entry
`(eff_of w, stage_of w)` followed by the STORED row: the derived one says what
calling the word performs, and the stored one says what its body does. A foreign
function's body is code this system has never seen, so `w_effs` gets
`[(eff_unsafe, SDynamic)]` and both propagate to every caller.

*Marshalling is checked at the declaration, not the call.* `i64` and `str` cross;
nothing else does, and `extern f ( bool -- )` is refused where it is written. The
host has no static information at the moment it performs an operation, so an
unmarshalable signature would otherwise surface as a stuck machine on some later
line, pointing at the call rather than at the mistake.

*The C table is fixed, not `dlsym`.* `bin/catcat_c.c` wraps six libc functions
and dune links it into the REPL; libc needs no `-l`, since every OCaml executable
already has it. Calling an ARBITRARY symbol needs libffi to build a call frame at
runtime, which is a dependency and a large surface for a demonstration whose
point is that the effect system carries foreign calls. Nothing above `perform` in
the host loop would change if the table became libffi — which is the claim the
fixed table is there to make cheaply.

*The host dispatches on the EFFECT, not the word id.* It had compared against
`w_print`/`w_read`, which worked because there were two. `extern` allocates a
fresh id per declaration, so the host asks `E06.susp_op_eff` and then
`E06.susp_op_name` for the symbol. Those two functions are the whole host
interface; letting `bin/catcat.ml` reach into `su_sess.se_nenv` would tie it to a
record that has already changed twice.

*A declared `extern` the host does not implement fails at the CALL*, reported as
"escaped with no handler in scope". That is not a gap in the framing but the
framing working: the host is the outermost handler and it declined.

---

## D-67. Recursion is `recurse` plus the `Rec` effect. Conditionals stay in the core.

Two halves of one request, answered differently, and the difference is the point.

### Recursion: a Dictionary word that cannot be inlined

`define f … { … f … }` never worked, and the reason is exactly the one the
request names. A program is a concatenation of primitives and operation calls,
`TWord w` denotes `Op w` (D-60), and resolving a word statically is `M04.handle`
run at elaboration time — which for a self-reference does not terminate. Named
recursion is not awkward here by accident; it is the one case where the ambient
Dictionary CANNOT supply a meaning early.

So the answer is the annotation D04 already has. A self-calling word gets
`od_stage = SDynamic` instead of `SStatic`: its meaning is supplied at runtime by
frame lookup, which `R02.step` already does for `WDef`, rather than by inlining.
**`!Rec` is not a mechanism added for recursion. It is the existing static/dynamic
tier at the one value where the answer has to be "later".**

*Why its own reserved id (4) rather than `Dict` at `SDynamic`.* Semantically the
latter is deeper — recursion IS dictionary resolution deferred. But `row_visible`
elides only a STATIC `Dict` entry, so a dynamic one would start printing `!Dict`
on every recursive word and every caller, and D-37's whole claim is that `!Dict`
is never written. A separate `Rec` keeps that promise and says the useful thing:
not "resolved late" but "may not terminate". Koka spells the same effect `div`.

*`recurse`, not the word's own name.* Forth's `RECURSE`, for Forth's reason — the
name is not in scope inside its own body. Keeping it anonymous is not deference to
tradition: binding the name would silently change what
`define f { 1 }  define f ( … ) { f }` means, turning a program that already
parsed into a different one. `recurse` collides with nothing and exists only
where it means something. `E05.locate` prints it back as `recurse` too, so the
round-trip that module claims survives a self-call.

*A recursive word must declare its signature.* Inferring it is solving a fixpoint
and this elaborator composes signatures left to right. `define f { recurse }`
says so rather than reporting "unknown word", because the difference between a
missing import and a missing signature is the whole of the diagnosis.

*`!Rec` propagates and is not silenced by default.* Every caller of a recursive
word carries it up to the top level, which is correct and is what Koka does with
`div`. `handle Rec over ( ) init { } { } { … }` discharges it — an unproved claim
that this call terminates, exactly as much of a promise as `unsafe` is, and the
same shape. **No `terminates { … }` macro was added**, deliberately: `unsafe` is
needed because C cannot be called otherwise, whereas `!Rec` reaching `main` is
the normal and honest outcome, and sugar for silencing it would invite silencing
it.

`Unsafe` and `Rec` are now a pair: reserved effects with NO operations, never
performed at runtime, pure row markers that propagate by the ordinary rules and
are discharged by an ordinary handler. That is a shape worth naming, and it is
where an effect system earns more than an effect system usually does.

### Conditionals: already as close to an effect as they should get

The request asked for these too, and this is the part I would push back on.

`if` is ALREADY not a language feature: it is one entry in `E03.builtin_macros`,
the parser is generic over that table, and `macro` adds to it. What it expands to
is `PBoolSum` plus `TCase`, and `TCase` is the ELIMINATOR OF A PRIMITIVE TYPE —
sums are primitive (D01 §3.1) because a stack's shape is static and a sum has a
different shape per branch. Something has to eliminate them.

Making that an effect would mean the branches are handler implementations, so the
condition would have to sit inside the handled block and the program would read
backwards; it would need an effect per sum type; and it would forfeit
`M03.srow_join`, which is what lets branches of unequal depth agree
row-polymorphically. The gain would be uniformity with recursion, and recursion
is a different situation: its problem was that static resolution diverges, and a
conditional's does not.

*What is genuinely shared, and is now true:* neither is core SYNTAX. `if` is a
macro over a core eliminator; a loop is `recurse` inside one. Anonymous loops —
a `while { … } { … }` with no surrounding `define` — remain absent, because a
macro expands to terms and cannot create the declaration a self-reference needs
to name.

---

## D-68. Sum elimination is dispatch plus a handler. `TCase` is gone.

D-67 argued conditionals should stay in the core. That was answered: `if` stays a
macro, and the CORE ELIMINATOR becomes the effect/handler pattern. It does, and
the objection I raised turned out to be a design constraint rather than a
blocker — worth recording in that order, because the constraint is the load-
bearing part.

*The objection, and it was real.* `M04.op_impl` hands an implementation
`vstack (st @ op_pre)` and nothing else, so a handler implementation cannot reach
beneath the operation's arguments. A `case` branch can reach beneath the
scrutinee, and not exotically — `if { } then { pop 1 } else { … } endif` pops the
value under the bool, and `abs`, `fact` and `dec_if_big` all do it. Branches as
plain implementations would have broken every conditional in the language.

*The fix folds the frame into the DECLARATION.* Variant `i`'s operation is
declared `( variants[i] @ j.pre -- j.post )` where `j` is what `M03.srow_join`
computes. So `srow_join` did not disappear; it moved from computing a `case`'s
TYPE at each use to computing its operations' DECLARATIONS once. `M06.dispatch_ok`
then checks the declarations agree, which is cheaper than rediscovering the join.

*And one relaxation was forced, which is an improvement on its own.*
`infer_impls` tested `s.pre = st @ op_pre` by EQUALITY — the one place in the
language where a signature had to be written at a fixed depth instead of being
instantiated. It is now `impl_frame`: the body's signature framed by a recovered
residual `k` must give the declared one. Sound for the reason every other framing
is — a denotation is `r:seg -> vstack (pre @ r) -> free (post @ r)`, so
instantiating at `k` HAS the declared type — and it is what lets a branch that
ignores the stack beneath the scrutinee implement an operation declared at the
joined depth. Handlers generally benefit: an implementation may now be more
row-polymorphic than its operation.

*What the core lost.* `TCase variants branches` became
`TDispatch ops variants`, a LEAF. `M06.infer_branches` and `M07.denote_case` and
`M07.dcase_arm` are deleted, not rewritten; what replaces them is `infer_impls`
and `M04.handle`, which effects already needed. Every induction over `term` lost
its branch-list case. `M07`'s clause is now one `Op` node with the same shape as
`TWord`'s and needs no `append_assoc` at all, because by the time it runs the
declarations have already made the shapes agree. `R02`'s step is
`KTerm (TWord (index ops tag))` — where a case used to JUMP to a branch, it now
makes a CALL, and the branch is found by `find_handler` like any implementation.

*Two inversion lemmas, and they are the same shape.* `lemma_dispatch_op` turns
`dispatch_ok`'s list walk into a fact about the one index a runtime tag selects;
`lemma_impl_typed` does the same for `impl_lookup`. Both exist because a fold
over a list is the wrong shape for a consumer that indexes into it.

*Ids come from a positional budget, not a threaded counter.* Each term gets a
`base` and hands `base + sterm_size t` to its successor, and
`sterm_size (StCase bs) = 1 + length bs + …` is exactly the `1 + n` ids a case
needs. So `E04` allocates without carrying mutable state. The EFFECT id is shared
by every case site (`R03.eff_case`) and does not need to be fresh: an inner
handler that does not implement an outer case's operation forwards it outward,
which `M04.fwd_impl` and `R02.find_handler` already do.

*Accepted costs, both real.* Declarations are at the FULL modelled shape either
side rather than the tightest one — sound, since `impl_frame` frames each branch
to it, but wider than necessary. And every `if` is now a handler frame plus an
operation dispatch at runtime rather than a direct branch, so D04's erasure (E3,
unproved) became load-bearing for the most common construct in the language.
That was priced before building; it is the bet D01 §1.2 already makes, now made
where it is most visible.

---

## D-69. A Dictionary carries bodies. E3 is blocked on `specialize`, not on effort.

Asked whether D04's E3 could be discharged. It cannot, and the reason is worth
recording precisely because it is not the reason it looked like.

*E3's type-level half is already proved.* `M06.lemma_static_specializes_to_pure`
shows that `TSpecialize`'s TYPING RULE takes an all-static row to an empty one.
What E3 adds is that the FUNCTION `specialize` implements what that rule
promises, and that needs `specialize` to exist.

*It could not exist, and not for want of effort.* `M10.dict` was

    { frames : list eff_id; stages : eff_id -> stage }

— which effects are present and at what stage, and nothing about what any of them
MEAN. `specialize env d t` is supposed to resolve `t`'s static effects against
`d`; with only a list of ids to resolve against, there was nothing to resolve
them TO. The omission survived because `specialize` was `assume val`, so nothing
ever had to consume a `dict`. That is the same failure mode as `M07.coherent`
(D-63): a placeholder nothing consumes is never tested.

`dict` now carries `d_defs : list (word_id & term)` — ONE table for words and
operations, because they are one namespace (D-01), so inlining a resolved word
and inlining a static effect's implementation are the same act on the same table.
Also de-closured (D-45); `stages` had no reason to stay a function once it had to
be built rather than described.

*E1 and E3 are now stated as types (D-64); E2 still cannot be.* E2 needs
`handle_d`, a fold of `M04.handle` over the dictionary's frames, and building it
needs each binding's DENOTATION — so E2 is stated in prose until `denote_static`
is applied to dictionary bodies.

### E3 does not say what D04 §4 claims it says

`M06.is_pure` is `Nil? row`: a statement about the ROW, not the residual term. A
`THandle` whose effect is discharged is already `is_pure` while its denotation is
full of `M04.Op` nodes.

That was always true and is now UNIVERSAL. Since D-68 every `if` elaborates to a
handler around a dispatch, so every conditional is a discharged handler with live
`Op` nodes underneath, and E3 is satisfied by such a program without erasing
anything at all.

So the zero-cost claim needs a second statement E3 does not make — that the
residual contains no handler frame for a static effect either — and that one is
FALSE for a case on a runtime tag, which can never be folded. The honest
resolution is that `THandle e [] TNil impls (TDispatch ops vs)` is a
syntactically recognisable shape, which is precisely what `E05.locate` already
matches, and a BACKEND compiles it to a branch. That is a compiler pass, not a
theorem about `specialize`.

### What `specialize` needs before E3 is attemptable

1. **Termination.** Inlining a self-referencing word does not terminate. D-67's
   `!Rec` marks that, and `all_static` therefore excludes directly recursive
   words — but D-67's check is syntactic self-reference only, so MUTUAL recursion
   is neither marked nor excluded. `all_static` is not currently sufficient for
   the inliner to terminate, and closing that needs the call-graph reachability
   over `w_defs` that M11's E5 also wants.
   **Closed by D-70**, and not by computing that reachability: the Dictionary is
   ordered, so `M05.word_bound` is the measure and mutual recursion cannot arise
   unmarked.
2. **Agreement between `d` and `env`.** Inlining `w` replaces a term of signature
   `w_sig w` by a body; E1 holds only if the body's inferred signature IS
   `w_sig w`. Nothing states that today, and it is the same shape of obligation
   D-63 removed by deleting `wenv`'s second signature table — which suggests the
   fix is again structural rather than a side condition.

---

## D-70. The Dictionary is ordered. `!Rec` is the opt-out, and mutual recursion needs no detection.

D-69 left `specialize` blocked on termination: inlining a self-referencing word
does not terminate, D-67's `!Rec` marked the direct case, and MUTUAL recursion
was neither marked nor excluded. The fix proposed there was transitive
reachability over the call graph. That is the wrong fix — it detects a condition
that should not be able to arise.

**A word may call only words defined before it.** Ids are handed out in
definition order, so the rule is `M05.word_bound body <= id`: one past the
highest word id the body calls, at most the word's own. `M05.ordered_at` is that
test and `M10.dict_ordered` lifts it to a whole dictionary.

Three consequences, and the third is the one that matters:

1. **`specialize` gets its measure for free.** Resolve every call to the highest
   word in `t` at once (`subst_words` is already a simultaneous substitution) and
   the result has strictly smaller `word_bound`, because each body substituted in
   is ordered strictly below the word it defines. The recursion is on that
   measure and no call graph is computed.
2. **D-67's detector is replaced, not kept.** `M05.mentions_word` is gone.
   `E06.install_def` now asks `not (ordered_at id t)`, which catches `recurse`
   for the same reason it always did — `recurse` compiles to `TWord id`, which
   is not below `id`.
3. **MUTUAL RECURSION CANNOT ARISE, so nothing has to detect it.** For `f` and
   `g` to call each other, one of them must name a word defined after it, which
   breaks the ordering and takes the same `!Rec` mark as a self-call. The
   transitive reachability D-69 asked for was the machinery needed to establish
   an invariant that is now simply true by construction.

`!Rec` is the opt-out, exactly as before: a word that breaks the ordering is not
rejected, it is resolved at runtime by frame lookup instead of by inlining, and
says so in its signature. Since a declared effect list is checked against the
inferred one, writing `!Rec` is mandatory once a signature is written —
`define fact ( i64 -- i64 ) { … recurse … }` is refused with "declares no
effects but its body has !Rec".

**Case operation ids moved BELOW the word being defined.** `E06.case_base` was
`se_next + 1`, putting a body's `case` operations above the word's own id; a
`TDispatch` is a call (D-68), so under the ordering test every conditional body
would have been marked `!Rec`. `case_base` is now `se_next` and `self_id` is
`case_base + sterms_size body`, so the word takes the id just past its own
budget. This is also why `word_bound` counts dispatch targets where
`mentions_word` returned `false` for them: that was wrong as well as incomplete,
and harmless only because of the allocation order it has now replaced.

*What this does NOT close.* Forward declaration — naming a word before defining
it — would reintroduce genuine mutual recursion, and it would arrive marked
`!Rec` rather than undetected, which is the point. Anonymous recursion (a block
that calls itself) still has no spelling.

---

## D-71. Failure is an aborting effect, and aborting is its own eliminator.

Asked for the effect analogue of `Option`/`Result`: one operation (`fail`), a
`try`/`catch` structure, the try block's outputs matching the catch block's, the
try block discarding everything it built on failure, and the catch block taking
no inputs.

### The one thing that could not be a handler

Every constraint above falls straight out of the existing machinery except the
central one. `fail` means "do not run the rest of the body", and the rest of the
body exists in exactly one place: the continuation `M04.handle` is holding when
it reaches the `Op` node. Handling an abort means DISCARDING that continuation.

Discarding is not capture — nothing is stored, returned, resumed or run twice,
so D-36 is untouched. But it is not something an `M04.op_impl` can express
either. An implementation is handed `st @ op_pre` and must produce `st @
op_post`; a `catch` block has to produce the result of the WHOLE handled
computation, which is a type the operation's declaration cannot mention.

Making `M04.handler` able to express it means indexing the record by the result
type of the code it handles. **That would break D03's identification, not
support it.** A method table, a typeclass dictionary, a module implementation —
none of them depends on the result type of its caller, and a `handler` that did
would no longer be the same construct wearing five hats. So the abort gets its
own eliminator and the identification stays exact:

    TTry : eff:eff_id -> pre:seg -> body:term -> catch:term -> term

with `M04.handle_abort` the second fold over `free`, differing from `handle` in
one clause. Exceptions being the odd one out in an effect system is a known
fact; what is worth recording is *which* property they cost, and that paying
for it in a separate constructor is cheaper than paying for it in `handler`.

An ABORTING EFFECT is one all of whose operations abort — there is no
per-operation flag. `Fail` (reserved id 6) has one operation; nothing in the
construction depends on that, so a `Break`/`Continue` pair is the same shape.

### What each piece contributes

* `M06.infer` checks `pre` against the body's own `pre` rather than trusting it,
  requires `catch` to consume nothing, and requires it to produce the body's
  `post`. The composite's signature is the body's, so a `try` is transparent to
  its context, and its row is the body's minus `eff` plus `catch`'s own — a
  `fail` inside a `catch` reaches the next `try` out.
* `M07`'s clause gets the saved stack for free: `vsplit` cuts the body's
  arguments off `stk` and denotes `catch` at the residual. Nothing else.
* `R02` needs telling. Its stack is flat, so `KTry e catch saved` records
  `drop (length pre) stk` at push time, and `find_try` takes the TAIL of the
  continuation at the boundary — which is what discards the frames between.
  `find_handler` stops at a `KTry` for the same effect so the innermost frame
  wins.
* `E03` adds `try { … } catch { … }` as a built-in macro. No terminator, and
  none is possible to need: `catch` is mandatory, so there is no alternation
  point and no ε-branch, which is the whole of why `if` needs `endif` (D-34).

### Two restrictions, both real, both stated rather than hidden

**`fail` is `( -- )`.** It composes with anything, so guard-style use works:
`dup 0 = if { } then { fail } else { } endif /` is `safediv`. What it cannot do
is stand where a value is expected — `if { } then { 1 } else { fail } endif` is
rejected, because the branches disagree. A `fail` usable there is one typed at
the empty type, and the core is monomorphic (D02 §5). This is the same missing
feature as the typed `catch` block: both arrive with generics.

**The try block runs on a fresh stack.** `M05.TTry` carries the body's `pre` and
the elaborator cannot compute it: its shape model is one concrete stack, so it
knows what a block LEFT but not how deep the block reached. `StCase`
over-approximates its declarations to the full modelled shape and is safe doing
so because `M06.impl_frame` frames the branches back down; the same
over-approximation here would make an abort discard the caller's entire stack
and `catch` responsible for rebuilding it. So `E04` elaborates both blocks at an
empty entry shape, `pre = []` holds by construction, and a body that reaches out
gets "the stack is empty" rather than a wrong answer. The CORE is not restricted
— `pre` is a field — so lifting this is an elaborator change alone.

### Where this leaves the "free Option monad" framing

The user's reading — operations before the `fail` run normally, operations after
it are inside the monad and need not be resolved — is exactly what `handle_abort`
does, and the sum-typed reading of it is the COMPILED form rather than the core
semantics: a backend may turn `TTry` into a `TDispatch` on an `option`-shaped
sum by CPS-ing the body at each `fail` site. That is the same division D-69
found for E3, where the zero-cost claim turned out to be a backend peephole on a
recognisable shape rather than a theorem about `specialize`.

---

## D-72. `Fail` is a monad in the ordinary way. The variable is the fold, not the bind.

A refinement of D-71, prompted by the observation that `Fail` is a monad in the
same sense the free list monad is, and that the effects built so far do not
affect the execution of the pure code around them while this one must.

The second half is right about the behaviour and worth being exact about where
it comes from, because the natural description of it is subtly misleading.

### Nothing is added at the bind

The description that suggests itself: once a word carries `!Fail`, the sequel has
to be lifted into a failure monad and monadically bound with the `fail`, so that
it becomes a no-op. Right conclusion, wrong mechanism — because **that bind
already exists and is not specific to `Fail`.**

`M04.fbind` puts the sequel inside the operation's continuation; that is what a
free monad's bind IS, and `M07` defines juxtaposition to be `kcomp`, so `fail w`
denotes `Op fail arg (fun r -> fbind (k r) (denote w))` with no special case
anywhere. The row is already right too: `M06.infer`'s `TSeq` rule takes the
`row_union`, so composing a `!Fail` word with a pure one yields a `!Fail` word.
That is the "the following word gets converted to a `!Fail` word" step, and it
is the ordinary rule doing it.

So the sequel is not typechecked as dead, and should not be. `fail` is `( -- )`,
the composition proceeds as if it returned, and `!Fail` propagates outward
through ordinary code by the ordinary rules.

### The deadness belongs to the handler

This was the right instinct and it is what is implemented. `handle_abort`'s one
distinguishing clause drops `k`, and

    M04.lemma_abort_kills_sequel :
      eff_of env op == eff ==>
      handle_abort eff catch (fbind (Op op arg k) f) == catch

says it exactly: `f` is arbitrary and does not appear on the right, so the code
after a `fail` cannot affect the result. Proved by conversion, since the
continuation `fbind` built is discarded rather than compared — which is why this
one escapes the wall that stops M10's H2 and H3. `lemma_abort_kills_kcomp` is
the same fact in the form the language composes in.

The converse half — that an operation of another effect passes through untouched
— is stated in prose in `M04` and NOT mechanized. It needs `extensionality`,
hence the continuation by projection, hence `Op?.op` of a term headed by the
guard `eff_of env op = eff`, which conversion cannot decide. That is H2/H3's
obstruction met in the abort fold, so it is one missing piece and not three.

### Where the multiplicity of `k` lives

Stated as a table because it is the whole design in one place:

| Times the rest of the program runs | Fold | Capture? |
|---|---|---|
| once | `handle` — implementation returns, fold continues into `k res` | no |
| zero | `handle_abort` — `k` dropped | no |
| many | free *list* monad, `choose` | **yes**, excluded by D-36 |

`Fail` and nondeterminism are the same family, and `Fail` is the other member of
it that survives the no-continuations rule. That is why the boundary falls where
it does, and it makes D-36's cost precise: what is given up is many-shot, not
zero-shot. Many-shot stays available with the multiplicity reified as a value —
an operation returning a list, or alternatives as delimited blocks the handler
schedules — because then there is nothing to capture.

### What a compiler would do, and what the interpreter does instead

`R02` discards the dead frames when the abort fires: `find_try` returns the tail
of the continuation at the boundary, so everything between is dropped. It is
built first and dropped after, which costs a walk.

A backend should not do that, and the lemma is the licence not to. The pass is
decidable and scoped: inside `TTry eff pre body catch`, any `TWord w` with
`eff_of w = eff` certainly aborts, so in `TSeq a b` with `a` certainly aborting,
`b` is unreachable and may be deleted. Note it is decidable only *inside* a
`TTry` — nothing marks an effect as always-aborting, since aborting is a
property of who handles it (D-71), so the analysis has the enclosing `try` as
its context rather than the effect declaration. That is another entry on the
list D-69 started: things that look like theorems about `specialize` and are
really backend passes over a recognisable shape.

---

## D-73. Macro hygiene is a well-formedness check. `if` is an ordinary macro.

Two things asked together, and they turned out to be independent of `!Dict` and
of each other. Both are done.

### Hygiene needs no renaming, because no `sterm` binds a local

The standard hygiene problem is a template's temporaries colliding with names at
the use site, and the standard fix is to rename them apart. Neither applies, and
the reason is a property of the surface language that had not been written down:

**`$x` is a READ. The only binder in the language is a signature parameter, and
a signature appears in a declaration, while a macro body is a term list.**

So a `$x` in a template naming no slot of its production cannot be a temporary
the author introduced — there is no way to introduce one. It can only read
whatever local encloses the expansion, which the author of a macro is in no
position to have meant. Renaming it apart would produce a read of nothing,
failing later and further from the mistake.

Hygiene is therefore `E02.mprod_stray`, checked in `ll1_extend` where a template
first exists, and the diagnostic quotes the name:

    catcat> macro bad ( { $b } ) { $b $tmp + }
    error: 'bad' reads $tmp, which names no slot of the production; a macro
    body cannot bind a local, so this would read the caller's $tmp. Add a slot
    for it, or correct the spelling

This is strictly better than gensym for the language as it stands: the error
names the macro rather than the call. **When `let` arrives (D05 §3.3) a template
will be able to bind and this becomes a genuine renaming problem** — the check
is the whole of hygiene only while the premise holds, and the premise is exactly
what will change.

### `if` was never blocked on anything

`if` carried `mp_builtin = true`, empty templates, and a hand-written
`expand_if` that `expand` dispatched to by name. The stated reason was that its
expansion is `StCase`, which has no surface spelling.

That confused two different things. **A template is a `list sterm` — an F*
value, not source text — so it can mention `StCase` perfectly well.** What
`StCase` lacks is a way for a *user* to type it, which is a fact about the
surface grammar and says nothing about whether the macro machinery can express
the expansion. Writing the two templates out:

    mb_body = [StVar "c"; StCase [[]; [StVar "t"]]]
    mb_body = [StVar "c"; StCase [[StVar "e"]; [StVar "t"]]]

reproduces `expand_if` exactly — `StVar "c"` is a block slot, so it splices the
condition's terms, and `subst_lists` fills the branches — and deletes:

  * `mprod.mp_builtin`, a field,
  * `expand_if`, a function,
  * the branch of `expand` that chose between the two paths,
  * `show_macro`'s `bodies` flag and the caveat line it printed.

`locate if` now shows its actual expansion, and it re-parses, because
`show_sterm` renders a two-branch `StCase` back as an `if`.

*What is still true:* a user could not declare this macro, because there is no
way to write `StCase` in source. Giving `case` a surface spelling is the
remaining step and it belongs with surface sums — a spelling fixed at two
branches would have to be redesigned the moment a sum has three, and a
two-branch `case` on a `bool` is all `if` needs.

*Correction to the assessment that preceded this.* I said the blocker was the
fresh operation ids each `case` site needs, and that macros would need gensym to
allocate them. That was wrong: `E04` allocates those ids from its positional
budget when it elaborates `StCase`, whatever produced the node. The blocker was
only ever the surface spelling.

---

## D-74. `specialize` is defined. The ordering is the algorithm.

D-69 said E3 was blocked on `specialize`, which was blocked on a dictionary with
bodies (fixed there) and a termination measure (fixed by D-70). Both were
prerequisites rather than difficulties, and with them in place the function is
eight lines.

    let rec resolve_below (d:dict) (n:nat) (t:term) : Tot term (decreases n) =
      if n = 0 then t
      else let w = n - 1 in
           let t' = match lookup_def d.d_defs w with
                    | None      -> t
                    | Some body -> inline_word w body t in
           resolve_below d (n - 1) t'

    let specialize env d t = resolve_below d (word_bound t) t

**One downward pass over the id space.** A word calls only words defined before
it, so a body spliced in at step `w` mentions only words `< w`, every one of
which a later step still has to visit. Descending is therefore enough: no
worklist, no fixpoint, no test that the substitution settled. `M11`'s
`lemma_specialize_chain` checks it on a three-link chain by `assert_norm`.

*The chain runs downward in id, and that is forced rather than convenient.* My
first attempt at that example had word 6 calling word 7 and asserted it resolved;
it does not, and F* said so. `dict_ordered` is exactly what rules that dictionary
out, so the failure was the design working.

### Fuel rather than the term, deliberately

Recursing on `word_bound` of the residual would be tighter and needs a lemma —
inlining the highest word strictly lowers the bound — which holds only under
`dict_ordered`. Counting down instead makes the function **total for any
dictionary**, and turns a disordered one from a divergence into an
incompleteness: inlining a self-referential body at step `w` leaves the inner
call, because the pass has gone past `w` and never returns.
`lemma_specialize_unordered_leaves_a_call` states that as a fact rather than a
hope. A specializer that quietly leaves a call still produces a residual that
runs; one that loops does not.

The cost is a pass per id rather than per call. This is a specification; an
implementation walks the term once with the table in hand, and agreeing with
this is its obligation.

### `inline_word` is not `subst_words`

`M05` now has both, and the difference is why only one needed a termination
argument. `subst_words` renames a call to another call, which cannot change how
deep a term reaches; `inline_word` splices a body in, which can. `TDispatch` and
a `THandle`'s implementation keys are untouched by both — they hold ids rather
than `TWord` nodes, a dispatch target is chosen by a runtime tag so there is no
single body to splice, and rewriting an implementation key would change which
handler answers.

### `dict_agrees`, which is D-69's other blocker written down

    let dict_agrees env d = every (w, t) in d.d_defs has infer env t == Some (w_sig env w, _)

Inlining `w` replaces a term whose signature `infer` reads as `w_sig env w` by a
body; E1 holds only if the body has that signature. It is a hypothesis on E1 and
E3 rather than a refinement on `dict`, because a dictionary is meaningful without
an environment and tying them in the type would make every construction carry a
proof about the other.

**The row is deliberately not required to agree.** Inlining brings the body's
effects with it, which is precisely what makes a static Dictionary word cost
nothing at runtime. Only the stack signature is invariant — the same asymmetry
E7 records for `subst_words`.

### What it does not do, each for a stated reason

* Fold a dispatch on a known tag: needs the scrutinee to be a literal `PInj`,
  which is constant propagation over `TSeq` and separate work.
* Erase `PPack`/`PUnpack`: sound by M10's H4, which is not proved.
* **Discharge a `TSpecialize` node.** E2's domain constraint requires it, and the
  dependency is real: stripping the marker is honest only when the body has no
  static effect left, which is a question about `infer` of the RESIDUAL, and
  knowing the residual is well typed at all is E1. E1 comes first. Until then a
  `TSpecialize` passes through, visible in the output rather than silently
  discarded.

E3 now carries three hypotheses — `dict_agrees` for typing, `dict_ordered` for
completeness, `resolvable` for coverage — and each answers to something in the
definition rather than to caution. `specialize_typed` remains assumed;
`make admits` is down from five to four.

---

## D-75. One walk for a word, and the ambient Dictionary is its last frame.

Q-18's second step. `R02.step` had two paths for `TWord`:

    | Some (WDef body) -> SNext ({ code = KTerm body :: k; ... })   (* no walk *)
    | Some (WOp e)     -> (match find_handler k e w with ...)       (* walks *)

A `WDef` was spliced straight out of the runtime dictionary, so a handler frame
could override an *operation* but never a *defined word*. That is the runtime
half of `!Dict` which D-37 described and nothing implemented, and it was the
duplication Q-18 named.

**A `WDef` is now what the chain finds when it runs out.** A defined word is an
operation of `Dict` at `SStatic` (D-63), so it takes `M04.eff_dict`, walks like
anything else, and falls back to its stored body — which is `M04.fwd_impl`
reaching the end of the chain, spelled in the machine. A `WPrim` is the one entry
that still does not walk, and for a reason rather than by exception: a primitive
performs nothing, calls nothing and alters no control flow (`M05.prim_op`), so
there is no frame that could answer for it.

The elaborator needed the same correction. `E04.elab_impls` read `n_op = None` as
"a word, not an operation", contradicting the table D-63 built; it now defaults
to `eff_dict`, and `E06.prelude_effs` names `Dict` so a program can write it.

### What this buys, demonstrated

    catcat> define greet ( -- str ) { "hello" }
    catcat> define bye   ( -- str ) { "goodbye" }
    catcat> define shout ( -- str ) { greet "!" cat }

    catcat> with { greet bye } { shout }
    ok  "hello!"
    catcat> handle Dict over ( ) init { } { greet { bye } } { shout }
    ok  "goodbye!"

**That difference is D-37's two tiers, running.** Static `with` is
`M05.subst_words` over the block's own term — the block is `TWord shout`, so
there is no `TWord greet` in it to rewrite, and rebinding does not reach through
a definition. The dynamic frame is consulted where `greet` actually runs, which
is inside `shout`. Neither is a bug; they are the two answers to "when is this
word's meaning supplied", and now both are available.

A Dictionary handler may carry state, so it is a class instantiated over a word:

    catcat> define twice ( -- str ) { greet greet cat }
    catcat> handle Dict over ( i64 ) init { 0 } { greet { 1 + dup show swap } } { twice }
    ok  "12" 2

### The dynamic form is better specified than the static one

`E04` enforces E7's hypothesis for `with` by CHECKING, at elaboration, that the
two words have equal signatures — an ad-hoc test standing in for an unproved
theorem. The dynamic form needs no such check: `M06.infer_impls` types the
override at `st @ op_pre -- st @ op_post` against `op_of env.w_ops`, which is the
word's own declared signature. Type-safe rebinding falls out of the handler rule
that already existed.

### What is not done, and the obstacle is concrete

Q-18's third step was `with` as a derived form — `THandle eff_dict` discharged by
`M11.specialize` — deleting `E04`'s bespoke substitution case. It is blocked on a
module boundary rather than on design: `specialize` lives in M11, which opens M07,
and P03 verifies against M01–M06 plus R0x. The fix is to move the pure-syntax
half down — `inline_word` is already in M05 and `d_defs` is a plain association
list, so a `resolve_defs : list (word_id & term) -> nat -> term -> term` in M05
would let `E04` call it, with M10 and M11 wrapping it in `dict`. Worth doing, not
done here.

---

## D-76. `with` is a Dictionary handler. `subst_words` was not `specialize`, and is gone.

Q-18's third step. It was supposed to be a refactor and turned into a
correction, because implementing the runtime path (D-75) produced a
counterexample to a claim M11 had been making since it was written.

### The claim that was false

M11 said `M05.subst_words` IS `specialize` restricted to one kind of static
effect. It is not. A rename rewrites the calls the block itself writes; handling
the Dictionary effect reaches a call the block makes INDIRECTLY, because the
frame stays installed while the callee runs. As soon as both sides ran:

    with { greet bye } { shout }                    -- "hello!"
    handle Dict … { greet { bye } } { shout }       -- "goodbye!"

Two spellings of one construct disagreeing on a result is exactly what D-02 says
cannot happen. The claim was not merely unproved; it was false, and it survived
because until D-75 nothing could compare the two.

### What replaced it

`E04` elaborates `with { old new } { body }` to

    THandle eff_dict [] TNil [(old, TWord new); …] body

and nothing else — no rewrite rule in the elaborator at all. `E06.discharge`
then resolves that frame away with `M05.resolve_defs`, the SAME function
`M11.specialize` calls. One function, two call sites, which is the whole of
D-02 stated as an arrangement of code rather than as an analogy.

    catcat> define w ( -- str ) { with { g b } { s } }
    catcat> w
    ok  "bye!"
    catcat> locate w
    define w ( -- str ) {
      b "!" cat
    }

Static and dynamic now agree, and the residual carries nothing of the rebinding
— `s` is inlined, `g` is `b`, the frame is gone. Zero-cost demonstrated rather
than asserted, and this time it is the same mechanism at both stages.

### Three deletions, and the module boundary that forced one of them

* **`M05.subst_words`, `subst_words_list`, `subst_words_impls` are deleted.**
  Nothing renames a word any more; `inline_word` does strictly more. This is the
  second piece of dead spec surface found this way, after `M03.srow_join`
  (Q-18) — both times a construct moved on and left its helper behind.
* **E7 is withdrawn**, since it was a theorem about `subst_words`. Both halves
  have owners: the hypothesis is `M10.dict_agrees`, the conclusion is E1.
* **`E04`'s signature-equality check is no longer load-bearing.** It stood in
  for E7; `M06.infer_impls` now types each replacement at the operation's
  declared signature. The check is kept ONLY to locate the mistake in a message,
  and was relaxed from equality to `impl_frame` so it cannot reject a program
  the core accepts.

`M05.resolve_defs` had to move down from M11 for any of this to work. M11 opens
M07, and P03 verifies against M01–M06, so an elaborator that discharged a
Dictionary frame would have dragged the denotation into its dependency set. The
pass needs neither a `dict` nor the judgment — a table of bodies is an
association list — so it belongs in M05 beside `inline_word`, with M11's
`resolve_below` a one-line wrapper.

### How far it inlines is decided by definition order

The pass descends the ids once, so a replacement defined AFTER the word it
replaces is reached before the substitution that introduces it and survives as a
call; one defined before is inlined in turn. Both are correct and differ only in
how much code the residual carries. It is the same property that makes one
descending pass enough (D-70), and it is why `locate t2` still prints
`quiet quiet` for U01's transcript rather than the inlined body.

A `handle Dict` written by hand is left alone — it carries state or a real
initialiser, or it is meant to be dynamic. Only the shape `with` emits is
discharged, and `E06.discharge_dict` checks that shape rather than assuming it.

---

## D-77. Three modes of specification. And no, generics do not need a unifier.

Supersedes the surface half of **D-31** and settles the question Q-18 raised
about it. D-31's core claim survives; what it lacked was a way to write a stack
signature without also enumerating every effect, and an answer to what generics
do to "no unifier".

### The three modes

    define f { … }                      infer the stack effect and the row
    define f ( i64 -- i64 ) { … }       assert the stack effect, infer the row
    define f ( i64 -- i64 !IO ) { … }   assert both

The middle one did not exist. Writing any signature meant `deceffs = Some []`,
so a bare `( i64 -- i64 )` asserted purity whether or not the author meant it,
and you could not write a stack signature without first knowing every effect the
body could reach. The fix is that `E02.ssig.ss_eff` distinguishes ABSENT from
EMPTY — `option (list string)` where it was `list string` — which is the whole
of the change; `install_def` already took `deceffs : option (list eff_id)` and
already did the right thing with `None`.

It pays for itself immediately on recursion:

    catcat> define fact2 ( i64 -- i64 ) { dup 0 = if { } then { pop 1 }
                                          else { dup 1 - recurse * } endif }
    defined fact2 ( i64 -- i64 !Rec )

Before, writing the signature required knowing that `recurse` produces `!Rec`
(D-67) — an implementation fact standing between the author and a stack
annotation.

### The purity marker is a bare `!`

`( i64 -- i64 ! )` asserts the row is empty. The sigil present, its name
deliberately absent: the effect region is written, and there is nothing in it.

**`!Pure` was considered and is worse**, for the reason the request itself
named. It sits exactly where effect names sit, so it would have to be a name
that is not an effect — reserved against `effect Pure { … }`, exempt from the
propagation every other entry in that position obeys, and a special case in the
row machinery that exists to have no special cases. A bare `!` cannot be
confused with an effect because every effect has a name, and `!!` was rejected
for having no reading at all.

`E01` now lexes a bare `!` instead of refusing it. That was the right layer to
change: the lexer cannot know which region it is in, so rejecting there made a
legitimate spelling unlexable in order to give one context a better message.
`$` and `#` keep their errors, since a local and a type variable are both
references BY name and neither has an empty-name reading.

`! !IO` together is refused — an assertion of emptiness alongside a named effect
is a contradiction, not a row.

### Generics need no unifier, because generalisation is never inferred

Q-18 flagged D-31's "no unifier, no occurs check, no union-find" as a conflict
with generics. It is not one, and the reason is worth stating precisely because
it also decides how generics get built.

**A word is generic only if its written signature says so.** Mode 1 always
yields a monomorphic signature; there is no generalisation step, so nothing ever
has to compute a most-general type. Then:

* At a CALL SITE, a generic word's variables are instantiated by matching its
  declared pattern against the modelled stack. Matching, not unification: the
  pattern has variables, the target does not.
* Inside a generic BODY, the declared variables are **rigid** — skolems, not
  solvable slots. A call to another generic word matches its flexible variables
  against those rigid atoms.

So every constraint has the form `flexible := rigid`, in both directions of
nesting. A flat map solves it in one left-to-right pass: no occurs check,
because the target never contains flexible variables; no union-find, because
there are no flexible-flexible constraints; no constraint graph, because there
is no generalisation to postpone one for. D-31's claim holds verbatim, and the
`M03.unify` on segments stays what it is — prefix matching, unrelated to this.

**The pass structure is untouched too.** D-31's two passes exist because mode 1
must compute types before emitting terms; modes 2 and 3 hand the elaborator its
inputs and skip pass 1 (`elab_define` vs `elab_define_infer`). Generics change
neither, because a body being inferred is monomorphic, so pass 1 never sees a
type variable. Generics add one thing: a matching step at call sites in pass 2.

*What this costs.* `define pair { dup }` cannot yield `∀T. ( T -- T T )` — you
write `define pair ( #T -- #T #T ) { dup }`. D-31 already accepted the analogous
limit and called it correct; this is the same limit with the escape hatch made
explicit rather than absent.

### A silent drop, found by asking what the rule means elsewhere

`declare op ( i64 -- i64 !IO )` inside an `effect` block parsed, ignored the
effect region, and said nothing. An operation belongs to the effect that
declares it, so writing one there is meaningless — but meaningless and silently
discarded is exactly the defect `!Eff` had before D-66, and it is now an error.
Found only by asking what "effects inferred" should mean for a `declare`, and
discovering the region had never been read at all.

---

## D-79. Generics erase at elaboration. The instantiation machinery, built; the wiring, not yet.

D-77 settled the architecture — generalisation is never inferred, declared type
variables are rigid in a body and flexible at a call site, so instantiation is
MATCHING and needs no unifier. This turns that into code. **What is committed is
the machinery, verified and complete in itself; the surface syntax and the
instantiation pass are not wired, so generics are not yet usable from the REPL.**
Saying so plainly is better than a half-connected feature that appears to work.

### `M01.dtype` gains nothing, and that is the design

A type variable never reaches the core. `sty` gains one case instead:

    | StyFixed : dtype -> sty      -- a type that is already elaborated

Never parsed. It exists so that **instantiating a generic is a surface rewrite,
`sty` for `sty`**, with the concrete type coming from a call site's stack model
rather than from source text. The alternative — a `string -> dtype` map consulted
during elaboration — would have to be threaded through `elab_ty`, `elab_sig`,
`elab_terms` and the whole mutual block beneath it, to reach the two places a
body mentions a type at all.

Rewriting instead means an instance is elaborated **by the existing elaborator
with nothing added**: copy the generic's stored signature and body with the
variables replaced, and what comes out is an ordinary definition. That is also
the precise sense in which generics are erased before the core sees anything —
`M01` needs no variable case because no variable ever gets there.

### What is built

* `E02.tsub`, `subst_ty`, `subst_stys`, `subst_params`, `subst_ssig`, and
  `subst_tys` over `sterm`. The last exists to reach one field: a body mentions a
  type only in a handler's `over ( … )`.
* `E04.match_ty` / `match_tys` / `all_bound` — the call-site matcher.
* `E04.elab_ty` handles `StyFixed`, and its `StyVar` error stopped being "not
  supported yet": a variable that reaches elaboration was never bound, which
  after D-79 means it names no parameter of its own signature.
* `E05.show_sty` prints an instantiated parameter as the type it was bound to.

`match_ty` is where D-77's claim becomes an artefact rather than an argument. The
pattern is an `sty` and may hold variables; the target is a `dtype` from the
stack model and never can. So every constraint is `flexible := rigid` — a flat
map, no occurs check (nothing to occur in), no union-find (no flexible-flexible
constraints), no constraint graph. `all_bound` refuses a parameter that appears
only in the outputs: `( -- #T )` asks the call site to invent a type, and
refusing it is what keeps instantiation a matching problem.

### What remains, and the shape it should take

1. **Parse `define f[#T #U] ( … ) { … }`.** `[` is self-delimiting, so
   `f[#T` already lexes as three tokens and the three-way choice after a name
   (`[`, `(`, `{`) is LL(1) on the token in hand — no lookahead problem.
   `E02.sdecl` gains `SdDefineGen`.
2. **A generic table**, in `nenv` and the session: name -> (params, ssig, body).
   Nothing is elaborated at declaration; a generic is a template.
3. **The call site.** `E04.elab_terms`' `StWord` case, when the name is generic:
   match the declared inputs against the modelled shape, allocate an instance id
   from the positional budget, emit `TWord id`, and record the request.
4. **The request channel already exists.** `elab_terms` threads
   `dacc : list (op_id & op_decl)` for `case` operations; widening that element
   to a variant — a case operation OR an instantiation request — needs no new
   parameter and no change to the plumbing through `elab_branches`,
   `elab_impls` and `elab_handle_parts`. This is the observation that makes the
   remaining work small.
5. **`E06` fulfils requests**: substitute, elaborate, `install_def` at the given
   id. An instance body may call another generic, so this iterates with fuel.

### Two consequences to accept when it lands

**A generic body is checked at instantiation, not at declaration** — C++
templates, not ML. Checking at declaration would need rigid variables to be real
`dtype`s, which is exactly the pollution `StyFixed` avoids. The trade is
deliberate and the error messages will name the use site.

**No recursion in a generic**, because an instance is created per call site and a
self-call would request an instance of itself forever. `!Rec` marks recursion on
a monomorphic word by keeping it out of `d_defs`; there is no analogue here until
instances are shared by (name, substitution) rather than minted per site.

---

## D-80. Generics run. `define f[#T] ( … ) { … }`, monomorphised at each call site.

D-79 built the machinery; this wires it. Generics are usable from the REPL:

    catcat> define twice[#T] ( #T -- #T #T ) { dup }
    generic twice[#T]
    catcat> 5 twice
    ok  5 5
    catcat> "hi" twice
    ok  5 5 "hi" "hi"
    catcat> define swap2[#A #B] ( #A #B -- #B #A ) { swap }
    catcat> 1 "x" swap2
    ok  "x" 1

Three instances of `twice` exist after that transcript — at `i64`, `str` and
`bool` — each an ordinary monomorphic word. D-77's architecture, running.

### The four pieces, and the one that made it small

1. **`E03` parses `[#T #U]`.** `[` is self-delimiting, so `f[#T` is already
   three tokens and the choice between `[`, `(` and `{` after a name is made on
   the token in hand — LL(1) with nothing to look ahead at (D-30). A generic
   must write its signature: generalisation is never inferred (D-77), so an
   unwritten one would have nothing to generalise.
2. **`E04.nenv` gains `ne_gens`**, a third namespace. A generic has no
   `word_id` and cannot be called until instantiated, so it cannot live among
   words. Nothing is elaborated at declaration.
3. **The call site** matches the declared inputs against the stack model,
   takes the instance id from the term's own budget, emits `TWord id` and
   records the request.
4. **`E06` fulfils requests** before typechecking the caller, since `M06.infer`
   reads the instance's signature out of `w_ops`.

The piece that kept this small was noticing the request channel already existed:
`elab_terms` threads `dacc` for `case` operations (D-68), so widening its
element from `(op_id & op_decl)` to a variant — `GOp` or `GInst` — needed no new
parameter and no change to the plumbing through `elab_branches`, `elab_impls`
and `elab_handle_parts`.

**A `StWord`'s budget is exactly one id, which is exactly what an instance
needs.** That is a coincidence worth naming, because it is what lets an instance
be identified before it is built.

### What the checks caught, and where they fire

    catcat> define bad3[#T] ( #U -- #U ) { }
    error: bad3 declares no type parameter #U
    catcat> define bad1[#T] ( -- #T ) { }
    catcat> 1 bad1
    error: bad1: #T is not determined by the inputs, so a call site cannot say
    what it should be
    catcat> define boxy ( Box[i64] -- Box[i64] Box[i64] ) { twice }
    error: twice, instantiated: dup: this value's type is not Copy

The last is the design working rather than a limitation. A generic body is
checked **at instantiation, not at declaration** — C++ templates, not ML —
because checking earlier needs rigid variables to be real `M01.dtype`s, which is
exactly the pollution `StyFixed` avoids (D-79). So `twice` is fine at every
`Copy` type and fails at `Box`, per instance, with the capability rule doing the
work. Linearity is enforced across generics with no rule written for it.

`ssig_stray` is the one check that fires at declaration, because a `#U` naming
no parameter can never be bound and reporting it at a call site would blame the
wrong line.

### Two restrictions, both deliberate

**No conditional and no nested generic call inside a generic body**, checked
rather than assumed:

    catcat> define bad2[#T] ( #T -- #T ) { dup 0 = if { } then { } else { } endif }
    catcat> 1 bad2
    error: bad2: a generic body may not contain a conditional or another generic
    call yet

An instance takes the call site's one-id budget, so it has none of its own to
hand out; ids taken from anywhere else would sit ABOVE the instance and break
the Dictionary ordering (D-70), which would surface as a spurious `!Rec`. Both
cases are exactly "the instance's elaboration returned declarations", so one
test catches them and the message names the limit. Lifting it means sharing
instances by (name, substitution) and installing them from a region below the
caller — the same change that would allow recursion.

**No recursion in a generic**, confirmed as a decision rather than a gap. An
instance is minted per call site, so a self-call would request an instance of
itself forever. Not worth complicating for: compile-time evaluation of pure
words is the likelier route to what recursive generics would be wanted for.

`locate` shows a generic as its TEMPLATE, printed from the surface form since it
has never been elaborated, and round-trips — including named parameters and the
bare `!` of D-77. An instance has no name and appears in a caller as `#101`,
which is the honest rendering of a word no program can write.

---

## D-81. The ordering rule was stronger than anything needed it to be.

D-80 refused a conditional inside a generic body, and the reason given was that
an instance is named from the call site's one-id budget and so has no ids of its
own — anything its body allocates sits ABOVE it and breaks the Dictionary
ordering (D-70). That was an accurate description of the check and a wrong
description of the problem. **The check was over-strict.**

### What `specialize` actually requires

`M11.resolve_defs` rewrites a call only when `lookup_def` finds it. Completeness
of one descending pass therefore needs: for every `(w, t)` in `d_defs`, every
word in `t` **that `d_defs` also defines** is `< w`. A call to something the
table does not define — a `case` site's operation, a declared effect's
operation, a primitive — is never rewritten, so where it sits cannot threaten
completeness, let alone termination, which is on fuel regardless (D-74).

`M10.dict_ordered` said `M05.ordered_at w t`: EVERY call below `w`. It now says
`defs_bound d.d_defs t <= w`, which is the condition above and nothing more.
`M05.word_bound` stays as the syntactic over-approximation it always was.

### What it cost

Exactly the thing D-80 could not do. A `case` site's operations are `WOp`, so an
instance's conditional may sit above the instance and nothing is wrong:

    catcat> define pick0[#T] ( #T #T bool -- #T ) { if { } then { pop }
                                                    else { swap pop } endif }
    generic pick0[#T]
    catcat> 1 2 true pick0
    ok  1
    catcat> "a" "b" true pick0
    ok  "a"

and a generic body may carry effects and abort through them:

    catcat> define safe[#T] ( #T -- #T !Fail ) { 1 1 = if { } then { fail }
                                                 else { } endif }
    catcat> try { 9 safe } catch { 0 }
    ok  0

The instance's own body budget now comes from `se_next` like any other fresh
allocation, and its `case` operations are registered exactly as a definition's
are. Nothing else about instantiation changed.

### The session-side test, and the one id it must special-case

`E06.install_def` read `not (ordered_at id t)`; it now reads
`calls_later s.se_dict id t`, which counts only `WDef` entries. **`id` itself
counts too, and has to**: the word being defined is not in `se_dict` yet —
`install_def` is what puts it there — so `is_def` says no about the one id whose
self-reference is the whole point. `recurse` compiles to `TWord id`, and that is
the case that must not slip through. Checked against the binary — with the row
asserted empty, since a bare stack signature now INFERS it (D-77):

    catcat> define fact ( i64 -- i64 ! ) { … recurse … }
    error: fact declares no effects but its body has !Rec
    catcat> define fact2 ( i64 -- i64 !Rec ) { … recurse … }
    defined fact2 ( i64 -- i64 !Rec )
    catcat> 5 fact2
    ok  120

### What remains refused, now for a specific reason

A generic body may still not call another generic. That is not an artefact of
the old rule: **an instance IS a `WDef`**, so an inner instance placed above an
outer one is precisely the case the ordering forbids. Lifting it means
installing instances innermost-first with ascending ids and rewriting the
caller's `TWord` — a different change, and one recursion would need too, which
is why it is not being taken (the user's call: compile-time evaluation of pure
words is the likelier route to what recursive generics would be wanted for).

---

## D-82. Explicit instantiation: `f[i64 str]`

A generic may be called with its type arguments written out. The implicit form
`f` stays, and stays the default.

### Why, given that matching already worked

Because matching cannot reach every generic. `all_bound` refuses a parameter
that appears only in the outputs — `( -- #T )` is a request to invent a type,
and a call site cannot say what it should be — so `define mk[#T] ( -- #T )` was
declarable and uncallable. Writing the types is the missing information, in
exactly the sense D-31 means it for a recursive word's signature.

Two more things it buys, both of which were workarounds before:

* **Disambiguation.** The implicit form reads the types off the modelled stack,
  so it is the stack that decides. When that is not what the programmer meant,
  the written form says so and the mismatch is reported rather than obeyed.
* **The inference pass.** `E04.infer_terms` — the pass that gives an unsignatured
  `define` its signature — works with metavariables, and `match_ty` needs a
  concrete `M01.dtype` to match against. So an implicit generic call in a body
  with no written signature cannot resolve, and now says so with the fix in the
  message. An explicit one needs no stack model at all and simply works:

      catcat> define f { 4 twice[i64] }
      defined f ( -- i64 i64 )

### It is one path, not two

`E04.gen_call` takes the starting substitution as an argument. The implicit form
passes `[]`; the explicit form passes the written types, elaborated to
`StyFixed`. Everything after that is shared — and because `match_ty` treats a
parameter already bound to a `StyFixed` as a constraint to CHECK rather than a
binding to make, feeding `match_tys` a pre-filled substitution turns the written
types into an assertion about the stack for free:

    catcat> 1 twice[str]
    error: twice: the stack does not match its declared inputs

So an explicit instantiation is verified against the stack exactly as an
implicit one is, rather than believed. No second rule, no unifier — D-31 again.

### Syntax and LL(1)

`f[t1 t2 …]`, space-separated, mirroring the `[#T #U]` of the declaration (D-80)
and using `#` only where a parameter is bound. `[` is self-delimiting, so `f[i64`
is already three tokens and the decision to enter `parse_tyargs` is made on the
one token in hand — LL(1) with nothing to look ahead at (D-30).

The branch sits BEFORE the macro branch in `parse_terms`, deliberately: a macro
takes its slots from what follows its name, and `[` cannot begin any slot, so a
macro that lost this race could not have parsed anyway.

---

## D-83. An instance is spliced, not installed: generics ARE `TSpecialize`

A generic call site elaborates to `TSpecialize <instance body>` inlined in
place. The generic SCHEMA is the only thing the session names. An instance gets
no `word_id`, no `se_dict` entry, no `w_ops` entry and no `w_effs` entry.

### The mechanism

`E04` emits `TWord base` at the call site and a `GInst base name su` request.
That `TWord` is a **splice key**, not a call: no word with that id is ever
installed. `E06.install_instance` elaborates the instance and returns a binding
`(base, TSpecialize body)`; `E06.splice_insts` substitutes it into the caller
with `M05.resolve_defs` — the same substitution `with` uses (D-76).
`E06.discharge_dict` then discharges the `TSpecialize` node by running
`resolve_defs` on its body, so nothing about the instantiation survives into the
installed word:

    catcat> define twice[#T] ( #T -- #T #T ) { dup }
    catcat> define quad[#T] ( #T -- #T #T #T #T ) { twice twice twice }
    catcat> define deep[#T] ( #T -- #T ×10 ) { quad quad quad }
    catcat> define d64 ( i64 -- i64 ×10 ) { deep }
    catcat> locate d64
    define d64 ( i64 -- i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 ) {
      dup dup dup dup dup dup dup dup dup
    }

Three levels of nesting, and the residual is nine `dup`s. No words, no
dictionary entries, no trace of a type parameter.

### Why this is the right shape and not a trick

`M06`'s rule for `TSpecialize` is "keep the signature, drop the static effects".
Discharging the node by inlining is what makes that rule TRUE of the residual
rather than merely asserted of the term. The same `M05.resolve_defs` now serves
three callers — `with` at elaboration time, a generic instance at elaboration
time, and `M11.specialize` at any other time — which is D-02's "specialization
and JIT are one operation" with running witnesses instead of an analogy.

`M11.specialize` still passes the node through. That is E2's remaining gap and
is stated in M11's header; the elaboration-time specializer discharges it, the
mechanized one does not yet. They agree on what discharging means.

### What it removed

Every one of these was a consequence, not extra work:

* **Nested generics.** D-81 left them refused for a specific reason: an instance
  was a `WDef`, so an inner one placed above an outer one was exactly the case
  the Dictionary ordering forbids. Spliced code has no id, so there is nothing
  to order. The `calls_later` check in `install_instance` is **deleted**, not
  weakened, and both `outer[#T] { twice[#T] }` and the implicit
  `quad[#T] { twice twice twice }` work.
* **Three registrations.** `w_ops`, `w_effs` and `se_dict` all described a word
  no program could name. `M06` types the spliced body directly.
* **`locate`'s `#id` case for instances.** There is no id to print.
* **The one-id budget question.** A call site's `sterm_size` is 1 and stays 1
  however large the generic is, because the id it buys is a splice key. The
  instance's own `case` operations come from `se_next` when it is built.

### What it costs

Two calls at the same types build the body twice. That is what monomorphization
costs and it is the honest reading of `TSpecialize`; sharing identical residuals
is a job for a later pass over the core, not for the elaborator.

### Termination

`install_instance` and `install_insts` are mutually recursive and bounded by
`gen_fuel = 32`. A LIMIT, not a budget: D-79 rules out recursive generics, so a
program that reaches it has written one, and the number only decides how long it
takes to say so.

    catcat> define loopy[#T] ( #T -- #T ) { loopy[#T] }
    generic loopy[#T]
    catcat> 1 loopy
    error: loopy: generic instantiation nested more than 32 deep;
           a generic may not be recursive

Note that the schema is registered before its body is read, so a generic CAN
name itself — which is why the limit reports the real problem rather than
"unknown word".

---

## D-84. A declared signature may FRAME the body's, not only equal it

`E06.install_def` compared the body's inferred signature to the declared one
with `<>`. It now asks whether the declared one is a framing of it.

### Why equality was wrong

Every term in this language is row-polymorphic: `∀r. pre@r ⇒ post@r`. A body
that touches less than its signature says is not a mismatch, it is an
instantiation of the implicit row variable (D-04) at a segment the body ignores.
`( i64 -- i64 )` over a body of `( -- )` is a word that leaves its argument
alone, and there was no way to write one:

    catcat> define sh2 ( i64 -- i64 !IO ) { "hi\n" print }
    error: sh2 declares ( i64 -- i64 ) but its body has ( -- )

The constructs that need it most are the ones D-01 says are the same construct.
A handler implementation threads a state segment it may not read. A method takes
its receiver whether or not this method uses it. A generic instance is checked
against a signature written in `#T` at types the body never touches — `shout[#T]
( #T -- #T !IO )` over `{ "hi\n" print }` is precisely that, so D-83 needed this
before it could accept its own instances.

### The test is one that already existed

`M06.impl_frame got [] { op_pre = row.pre; op_post = row.post }`. `Some k` means
`row.pre = got.pre @ k` and `row.post = got.post @ k`, with `k` RECOVERED off
the declared `pre` by `strip_pre` rather than searched for. That is the same
function, at the same empty state segment, that frames a handler implementation
to its operation's declaration (D-68) — so the framing rule for definitions and
the framing rule for implementations are one rule, which they should be.

It is spelled `M06.sig_frames` and lives in the spec rather than in `E06`,
because three callers ask it: `install_def` of a written signature,
`install_instance` of a generic's, and M11's E1 of what `specialize` preserves.
One definition is what keeps those three the same rule.

Nothing weakens: the residual must be consistent across `pre` and `post`.

    catcat> define bad ( i64 -- str ) { }
    error: bad declares ( i64 -- str ) but its body has ( -- )

### The consequence for E1, now taken

`M06.infer (TWord w)` reads the DECLARED signature out of `w_ops`, while the
stored body has the smaller inferred one. Inlining `w` therefore replaces a term
by one with a more general signature — `define f ( i64 -- i64 ) { }` inlines to
a term of `( -- )`. M11's `e1_type` said the residual's signature is `==` the
original's, which that falsifies; it now says `sig_frames`.

This is the lemma stated at the right strength rather than a weakening forced on
it. "Specialization changes cost, never interface" means every context that
accepted the original accepts the residual, and framing says exactly that, since
`M06.compose` frames. Equality would additionally forbid the residual from being
usable in MORE places, which is not a property anyone wants.

---

## D-85. Identical instantiations are built once

`E06.install_instance` consults a cache keyed on the generic's name and what its
parameters were bound to, and a hit returns the very same term. Nothing else
about D-83 changes: an instance is still spliced, still has no dictionary entry.

### Why it is sound, which is the whole argument

Instantiation is a **pure function** of the schema, the substitution and the name
environment. `install_instance` reads none of the call site: not the modelled
stack, not the caller's signature, not where the splice will land. The instance
body is elaborated against its OWN declared signature — `elab_define … (subst_ssig
su g.g_sig) body` — so even the entry shape is a function of the key. Two
requests with equal keys therefore have equal answers, and the second may take
the first's.

The environment is the third argument and it is why the cache is **per
declaration, not per session**. A generic's body is elaborated against the names
in force when it is INSTANTIATED, and a later `define` may shadow a word that
body calls, so `(name, types)` does not identify a residual across declarations:

    catcat> define greet ( -- str ) { "hi" }
    catcat> define g[#T] ( #T -- #T str ) { greet }
    catcat> define a ( i64 -- i64 str ) { g }
    catcat> define greet ( -- str ) { "bye" }
    catcat> define b ( i64 -- i64 str ) { g }
    catcat> 1 a
    ok  1 "hi"
    catcat> 1 b
    ok  1 "bye"

A session-wide cache would have served `"hi"` to `b`. Within one declaration
`ne_words` cannot change — nothing between two lookups adds to it — so the key is
exact there, and that is also where the cost is: nesting is what multiplies, and
nesting happens inside one declaration.

Whether late binding is the RIGHT semantics is a separate question and is left
open (N02 Q-20). Pinning a schema to the environment of its declaration would
make the key exact forever; it would also change what shadowing means.

### The key has to be canonicalised

`inst_key` lists the bindings in the generic's DECLARATION order rather than
reading `su` off as it comes. The implicit form builds the substitution by
walking the declared inputs, so `( #B #A -- … )` binds `#B` first, while the
explicit form builds it in `[#A #B]` order. Two calls meaning the same thing
would otherwise miss each other.

### What it was actually costing

Exponential elaboration, not a constant factor. `deep` calling `quad` three
times, each calling `twice` three times, elaborated `twice` nine times — and it
compounds with depth. A chain `g0 … gN` where each body calls its predecessor
three times, `define top ( i64 -- i64 ) { gN }`:

    depth        6        8        10        12
    before      50 ms   2.9 s     228 s     >5 min (killed)
    after        5 ms     7 ms      27 ms    255 ms

### Recursion is now caught by name, not by depth

`gen_fuel` remains, because F* needs a decreasing measure for the mutual
recursion, but it is no longer what reports the error. `install_instance`
carries the chain of generics currently being instantiated and refuses a repeat:

    catcat> define loopy[#T] ( #T -- #T ) { loopy[#T] }
    catcat> 1 loopy
    error: loopy is already being instantiated; a generic may not be recursive,
           directly or through another

By NAME rather than by key, which is what makes it catch two cases depth could
only catch slowly: mutual recursion between two generics, and **polymorphic
recursion** — `f[#T]` whose body calls `f[Box[#T]]` has a different key at every
level, so a key-based check would never repeat.

### What is still duplicated, and where it now belongs

The RESIDUAL still carries one copy of the instance per call site; only the work
of building it is shared. But because the cache hands back the identical term,
those copies are now **structurally equal** rather than merely alpha-equivalent —
they have the same `case` operation ids and everything else. That turns sharing
them into ordinary common-subexpression elimination over the core, which is a
compiler pass, applies to every inlined term and not only to generics, and needs
no elaborator support. See N02 Q-19.

---

## D-86. A static Dictionary frame reaches into a generic instance

`with { bump big } { … stepper … }`, where `stepper` is a generic whose body
calls `bump`, used to do **nothing** — silently. It now rebinds, at any nesting
depth, and the residual shows the rebinding folded in:

    catcat> define bump      ( i64 -- i64 )        { 1 + }
    catcat> define big       ( i64 -- i64 )        { 1000 + }
    catcat> define inner[#T] ( #T i64 -- #T i64 )  { bump }
    catcat> define outer[#T] ( #T i64 -- #T i64 )  { inner[#T] inner[#T] }
    catcat> define reb ( -- str i64 ) { with { bump big } { "t" 0 outer } }
    catcat> locate reb
    define reb ( -- str i64 ) {
      "t" 0 1000 + 1000 +
    }

*Two causes, and both had to go.* `E06.discharge_dict`'s `THandle` clause
discharged the body against `defs` and only applied the frame afterwards, via
`resolve_defs (impls @ defs)`. But the `TSpecialize` clause **resolves its body
where it stands**, so an instance inside the block was specialized against the
ambient dictionary during that descent and there was no call left for the
substitution to rewrite. And `install_instance` ran its own `discharge` over the
spliced body, which resolved every NESTED instance at a point where no enclosing
frame exists or could — so even after fixing the first, a rebinding reached a
one-level instance and stopped at a two-level one.

*The rule, stated positively:* **inside a `with` block the ambient Dictionary is
the extended one**, so everything that consults the Dictionary — a direct call,
a nested `with`, a generic instance at any depth — consults the same table. The
frame is threaded down the descent instead of being applied only at the end, and
an instance is spliced but not discharged, leaving its resolution to whoever
uses it.

*Why this is not a change of meaning but a repair.* D-75 killed `subst_words`
because static and dynamic `with` disagreed on a result, and D-02 says that
cannot happen. This was the same defect wearing a generic: `handle Dict over ( )
init { } { … }` is discharged by the *same* clause — the stateless shape is what
`discharge_dict` tests for — so both spellings were wrong together and are now
right together.

*What still does not reach in, and why that is correct.* A **stateful**
`handle Dict` is a runtime frame, installed after the instance was built, and it
finds no call because the code was specialized at elaboration. That is not two
spellings disagreeing; it is one of them having already run. Specialization
commits, which is the whole point of it.

### The performance trap, and the flattening that pays for it

Leaving nested instances undischarged put a `TSpecialize` at every level, and
`discharge_dict` runs a full `resolve_defs` at each — itself `n` traversals of
its argument. On a depth-12 chain that triples at each level this went from
0.9 s to **7.2 s**, a factor of `depth`.

`unwrap_spec` strips the wrapper off an instance being spliced into ANOTHER
instance, because **specializing is idempotent**: a `TSpecialize` inside a
`TSpecialize` says nothing the outer one does not. `splice_insts` puts the
outermost wrapper back, which is where an instance meets a definition and where
D-83 needs the node. One node per top-level generic call, one resolution pass.

The same benchmark now runs in **0.58 s** — faster than before the fix, because
the redundant per-level resolution was there all along and the flattening
removed it. Measured, not reasoned: 10 / 65 / 583 ms at depths 8 / 10 / 12
against 12 / 91 / 901 ms before.
