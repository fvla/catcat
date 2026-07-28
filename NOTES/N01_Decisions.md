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

**D-28. `--` is self-delimiting, like the brackets.** D-15 originally made only
`{ } ( ) [ ] :` self-delimiting.
*Why the change:* found by building the lexer. With brackets alone,
`( i64--i64 )` lexed `i64--i64` as one word, so a tightly-written signature
failed to parse while `{$x $x mul}` worked. Both are structural punctuation;
the asymmetry was accidental. A *single* `-` is unaffected, so `-5` is still an
integer literal and `pop-all` still one word.

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
