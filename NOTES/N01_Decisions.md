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
