# D03 — Effects, Interfaces, and the Object Model

This document specifies the construct that D01 §1.1 identified as the design's
centre: one mechanism serving as effect system, typeclass system, object model,
module system, and namespace.

Mechanized in [M04_Effects](../P01_Specification/M04_Effects.fst) and
[M10_Handlers](../P01_Specification/M10_Handlers.fst).

---

## 1. Interfaces

An **interface** is a named set of word declarations with stack signatures:

```
interface Counter[#T] {
    declare create    ( -- #T )
    declare delete    ( #T -- )
    declare increment ( #T -- #T )
    declare count     ( #T -- #T i64 )
}
```

That is the whole construct. `declare` introduces a word with a signature and no
body; a handler supplies bodies later.

In the core this is an `eff_sig`: a set of `op_sig` records, each of which is
exactly a stack signature. Interface operations and ordinary words share one
typing rule (`TWord` in [M06](../P01_Specification/M06_Typing.fst)) — the type
checker does not distinguish them, which is the unification made concrete.

---

## 2. Handlers

A **handler** supplies implementations. One record type
([M10](../P01_Specification/M10_Handlers.fst)) serves every role:

```fstar
noeq type handler (env:sig_env) (eff:eff_id) (a:seg) = {
  h_ops : op:op_id -> op_impl env (op_of env op) a;
  h_ret : vstack a -> free env a;
}
```

**A handler never captures a continuation. It is a stateful object** (D-36). An
operation call runs its implementation, which *returns*; nothing is extracted,
saved or resumed. The handler carries a state segment, threaded through its own
implementations' signatures with the state types preserved:

```
implementation of  o  is typed at   ( args… state -- results… state )
```

So a stateful handler is not merely analogous to the class of §3 below — it is
the same construct, which is D-01 confirmed once more.

This is a correction. An earlier version of this section specified *deep*
handlers, whose implementations receive the continuation and may run it zero,
once, or many times. That is rejected: continuations must not be a runtime
construct in the compiled language. Everything a resume-exactly-once handler
can do is expressible by returning, and the object model is what the design
already wanted for classes anyway.

**Reentrancy survives the correction, and gets cheaper.** The draft's
requirement that "every effect is reentrant" is not a consequence of deep
handlers; it is the *installed-frame* property. `R02.step` runs an
implementation with the handler frame still in the continuation, so an
operation the implementation itself performs reaches the same handler. That
costs nothing and needs no capture. What it does need is a rule for re-entering
a handler *while its own state is lent out to a running implementation*, which
is reported as an error rather than served a stale copy (D-48) — the aliasing
question a linear language ought eventually to settle statically.

What is genuinely given up is nondeterminism in which one choice makes the rest
of the enclosing program run more than once. A free-list-monad effect remains
available with the multiplicity **reified as a value**: an operation returning a
list, or one whose alternatives are delimited blocks the handler schedules.
That is the form that survives compilation to a state machine, which is also
how coroutines are to be built (D-39).

The distinctions between the six roles are entirely about *when the handler is
resolved and whether it is erased* (D04), never about the mechanism.

---

## 3. The object model

A **class** is a handler whose representation is a sealed stack segment.

```
class CounterI64 : Counter[CounterI64] over ( i64 ) {
    caps { }                          -- neither Copy nor Drop: linear

    define create    { 0 pack }
    define delete    { unpack pop }
    define increment { unpack 1 add pack }
    define count     { unpack dup pack swap }
}
```

- `over ( i64 )` gives the **representation segment**. It may be any number of
  slots; `over ( f64 f64 )` would be a two-slot class, and no tuple type is
  involved (D02 §1).
- `caps { }` declares the exposed capabilities. Here: none, so `CounterI64` is
  linear.
- `pack`/`unpack` cross the class boundary. **`unpack` is well typed only inside
  the class body** — that is what "type access erasure" means concretely, and
  what makes the encapsulation real rather than conventional.

### Sealing is free

`vseal` and `vunseal` are mutually inverse
(`M02.lemma_unseal_seal` proves one direction), so a class boundary has no
runtime representation. Combined with the erasure theorem (D04 §4), a method call
through a statically resolved interface compiles to the same code as a direct
call — `increment` on a `CounterI64` becomes an integer add, with the class
gone entirely.

---

## 4. The Counter example, corrected

The draft's sketch, for comparison:

```
define-effect __Interface_Counter[T]
interface {
  declare-word new ( -- T ) ;
  declare-word delete ( T -- ) ;
  declare-word create ( -- T ) ;
  declare-word increment ( T -- T ) ;
  declare-word getCount ( T -- T int ) ;
} ;

instantiate-class Counter int (__Interface_Counter)
{
  define-word new  0 ;
  define-word delete  pop ;
  define-word create  new ;
  define-word increment  1+ ;
  define-word getCount  dup ;
}
```

Four problems, and what §1–§3 above do about them:

1. **`delete` is a no-op.** It is defined as `pop`, which merely discards a
   slot. If `Counter` is meant to be a resource, `delete` must be the *only* way
   to discard it — which requires the type to lack `Drop`. Fixed by `caps { }`:
   without `Drop`, `pop` is rejected at `CounterI64`, so `delete` is forced.
2. **`new` and `create` are redundant** — `create` is defined as `new`. Merged
   into one word.
3. **The representation is transparent.** `increment` as `1+` and `getCount` as
   `dup` operate on the `int` directly with no boundary crossing, so nothing
   distinguishes a `Counter` from an `int`. Fixed by explicit `pack`/`unpack`,
   which are erased anyway.
4. **`;` and the `__`-prefixed interface name** are Forth-isms the design does
   not need. `{}` delimits (D05), and the interface is just `Counter`.

The corrected version is §3 above.

---

## 5. Linearity

Types carry capabilities: `Copy` licenses `dup`, `Drop` licenses `pop`. A type
with neither is **linear** — it must be consumed exactly once, by a word that
explicitly takes it.

`Clone` is deliberately *not* a capability. It is an ordinary interface — a word
you call — exactly as in Rust. Only `Copy` and `Drop` are consulted by the
compiler, and they are consulted in exactly two typing rules (D02 §7).

Capability derivation ([M01](../P01_Specification/M01_Kinds.fst)):

- Primitives have both.
- A **sealed type has exactly what it declares** — this is the narrowing that
  makes the object model useful.
- A sum has a capability when every variant's payload has it.

**Why narrowing is sound.** A sealed type exposing fewer capabilities than its
representation cannot have the missing ones recovered by any client, because
`unpack` is well typed only inside the class body. So a linear `Counter` over a
copyable `i64` is a genuine guarantee (M10, obligation H5).

The stack contributes *affine slot use* — a value is consumed when popped — but
that is not linearity by itself, because `dup` and `pop` exist. The capability
system is what supplies the rest. This is the correction from D01 §3.3.

**Worked instances: `Box` and `Rc`.** D02 §1 adds pointer types for recursion
(`TBox`, `TRc`), and they are built out of exactly this machinery rather than
needing any of their own. Both have **neither `Copy` nor `Drop`** (M01
`has_cap`), so both are linear:

- `Box[t]` cannot be duplicated — that would alias a unique pointer — and
  cannot be discarded by `pop`, because freeing it is an operation, not a
  no-op. Its two legal operations, allocate and open, are ordinary words
  (`PBoxNew`/`PBoxOpen`).
- `Rc[t]` cannot be a bitwise `dup` either, because cloning a shared pointer
  means incrementing a refcount, and cannot be a silent `pop`, because
  dropping one means decrementing it. `clone` and `release` are interface
  words (`PRcClone`/`PRcDrop`), exactly the `Clone`-as-interface-word shape
  above, not compiler-recognized capabilities.

This is not a new mechanism bolted on for pointers — it is capabilities-plus-
`Clone`-as-an-interface-word, unchanged, applied to a type that happens to wrap
an unsafe primitive. The design confirms itself here rather than growing to
accommodate `Box`/`Rc`: the shape was chosen (D-08) before either type existed.

**The recurring pattern.** Expect the same treatment for every future type
that wraps something unsafe: a file handle, a socket, an mmap'd buffer, a GPU
allocation. Give it neither `Copy` nor `Drop`, and expose its real operations
— open, clone, close, release — as interface words instead of relying on `dup`
and `pop` to mean something safe. `Box`/`Rc` are the first instance of this
pattern, not a special case of it (D-26).

---

## 6. Effect rows

```fstar
type erow = list (eff_id & stage)
```

Rows are implicit in signatures, like stack rows. Effects propagate through
composition (union) and are discharged by handling (removal). A caller must
either propagate a callee's effects or handle them — the draft's rule, unchanged.

`stage` (`SStatic` / `SDynamic`) records *when* the effect is resolved, and is
the annotation the zero-cost theorem quantifies over (D04).

**Purity is the empty row**, and it is real: a program with an empty row denotes
a computation containing no operation nodes at all (M07, obligation T4). An
effect system that could not prove this would not be worth having.

---

## 7. Built-in effects

Effects the compiler knows about, all declared through the same interface
mechanism:

| Effect | Stage | Notes |
|---|---|---|
| `IO` | dynamic | The usual side effects. |
| `Alloc` | dynamic | Heap allocation; absent row means no allocation, which is checkable. |
| `Mut` | dynamic | Mutable state. |
| `Dyn` | dynamic | Dynamically-scoped variables (`$*x`, D05 §3). |
| `Dict` | **static** | Word rebinding. Static by default — this is D01 §3.5. |
| `Parse` | static | Macro effects on the lexer/parser (D05 §5). |
| `Compile` | either | Access to compiler stages. Dynamic use is the JIT (D04 §5). |

`Dict` and `Parse` being static is what keeps elaboration decidable and the LSP
fast. `Compile` is the one effect that is genuinely useful at both stages, and
D04 §5 explains why that is the design working rather than an exception to it.

Sums are needed to back several of these: `IO` results, `Alloc` failure, and
handler dispatch all need a value whose shape varies at runtime. This is the
concrete reason sums must be primitive (D01 §3.1) rather than encodable.
