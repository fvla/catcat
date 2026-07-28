# U02 — Word Reference

Every word the language provides today. That is a short list: eleven primitives,
two constants, and three stack shuffles.

> **Current as of commit `ff01d06`.**
> Source of truth:
> [E05_Repl.fst](../P03_Elaboration/E05_Repl.fst) `prelude_nenv` (names and
> signatures), [R03_Prelude.fst](../P02_Reference/R03_Prelude.fst) (word ids and
> the dictionary), [R02_Machine.fst](../P02_Reference/R02_Machine.fst)
> `apply_prim` (semantics), [E04_Elaborate.fst](../P03_Elaboration/E04_Elaborate.fst)
> `elab_terms` (the shuffles). If this file and those disagree, they are right.

Signatures follow the surface convention: **bottom-to-top, top of stack on the
right.** `( i64 i64 -- i64 )` takes its right-hand argument from the top.

---

## 1. Arithmetic

| Word | Signature | Meaning |
|---|---|---|
| `+` | `( i64 i64 -- i64 )` | sum |
| `-` | `( i64 i64 -- i64 )` | difference, `below - top` |
| `*` | `( i64 i64 -- i64 )` | product |
| `/` | `( i64 i64 -- i64 )` | quotient, `below / top` |
| `%` | `( i64 i64 -- i64 )` | remainder, `below % top` |

**Operand order.** The top of the stack is the *right* operand, so `10 3 -` is
`10 - 3 = 7`, not `-7`. Same for `/` and `%`.

**`/` and `%` are Euclidean**, so the remainder is never negative for a positive
divisor:

```
-7 2 /      ->  -4          \ floor, not truncation toward zero
-7 2 %      ->   1          \ non-negative
```

This is inherited from F*'s mathematical `int` and is **not yet a decision**.
The numeric tower — wrapping, saturation, division rounding, IEEE-754 — is an
open question (N02 Q-06), and these are properties of *operations* that belong
in a module the spec does not yet have. Do not rely on it.

**Division and modulo by zero get stuck** rather than trapping or returning a
value: `3 0 /` reports `STUCK: division by zero`. The type system does not rule
it out, so the reference machine reports it instead of guessing.

**There is no float arithmetic.** `f32`/`f64` are valid types with no operations
on them, deliberately: IEEE-754 semantics are unsettled, and a reference
implementation that guessed would become the de facto specification.

---

## 2. Comparison

| Word | Signature | Meaning |
|---|---|---|
| `<` | `( i64 i64 -- bool )` | `below < top` |
| `<=` | `( i64 i64 -- bool )` | `below <= top` |
| `=` | `( i64 i64 -- bool )` | equality |

There is no `>`, `>=` or `!=`. The first two are `swap <` and `swap <=`; the
third would be `= not`. **`!=` can never be spelled** — `!` opens the effect
sigil, so no word may begin with it.

---

## 3. Logic

| Word | Signature | Meaning |
|---|---|---|
| `not` | `( bool -- bool )` | negation |
| `and` | `( bool bool -- bool )` | conjunction |
| `or` | `( bool bool -- bool )` | disjunction |

Spelled as words, not `&&`/`||`, because they read better in postfix and there
is no precedence to disambiguate.

| Word | Signature | Meaning |
|---|---|---|
| `true` | `( -- bool )` | the true constant |
| `false` | `( -- bool )` | the false constant |

`true` and `false` are **ordinary words**, not literals — bound in the prelude
to a definition whose body is a boolean literal. Making them words costs
nothing, since specialization inlines a definition that is just a literal, and
it means they shadow like any other name and neither the lexer nor the
elaborator needs a case for them.

Booleans are what `if` consumes; see [U01](U01_Grammar.md) §4.

---

## 4. Stack shuffles

These are not dictionary entries. They are **elaborator forms**, instantiated
from the compile-time stack shape into monomorphic core operations — the core
has no polymorphism, so `dup` on an `i64` and `dup` on a `bool` are different
terms.

| Word | Effect | Requires |
|---|---|---|
| `dup` | `( a -- a a )` | `a` is `Copy` |
| `pop` | `( a -- )` | `a` is `Drop` |
| `swap` | `( a b -- b a )` | — |

The capability requirements are the whole of linearity (D-08): a type with
neither `Copy` nor `Drop` is linear, and the errors say which is missing.

```
catcat> define b ( Box[i64] -- ) { pop }
error: pop: this value's type is not Drop; consume it explicitly
```

`rot` is idiomatic and **not implemented**. Deep access exists in the core as
`pick`/`roll` but is reachable only through named parameters (`$x`), never
directly — which is the intent: locals exist so that deep shuffling does not
have to be written by hand.

---

## 5. Types

| Type | Notes |
|---|---|
| `i8` `i16` `i32` `i64` | `i64` is what integer literals produce |
| `u8` `u16` `u32` `u64` | valid; no operations |
| `f32` `f64` | valid; no operations (§1) |
| `bool` | `true`/`false`, or a comparison. Consumed by `if` |
| `unit` | valid; no literal |
| `Box[t]` | owning unique pointer. Neither `Copy` nor `Drop` — linear |
| `Rc[t]` | shared refcounted pointer |

`Box` and `Rc` exist so that recursive types can be written at all: recursion is
legal only *through* a pointer, exactly as in Rust. **No surface word constructs
one yet** — the types are usable in signatures, the values are not yet
reachable.

A pointer's capabilities do not depend on its pointee, which is what lets the
type system stay environment-free.

---

## 6. Defining words

```
define sq { dup * }                              \ signature inferred
define sq ( i64 -- i64 ) { dup * }               \ signature asserted
define hypotsq ( $x:i64 $y:i64 -- i64 ) { $x $x * $y $y * + }
```

Definitions may shadow prelude names — nothing reserves `+`, `true` or `false`.
`define` itself is not a reserved word either; it is recognised by position at
the start of a declaration, and the same is true of `if`, `then`, `else` and
`endif`, which are keywords only inside a conditional.

Grammar, locals, and the inference rules are in [U01](U01_Grammar.md).

---

## 7. The REPL

```
make catcat
./_build/default/bin/catcat.exe
```

Arguments are executed as successive lines and the program exits, which is how
the regression tests run:

```
./_build/default/bin/catcat.exe '2 3 +' 'define sq { dup * }' '6 sq'
```

The stack persists between lines and is shown bottom-to-top after each, or
`(empty)`. **A parse or type error leaves the session untouched**, so a mistyped
line cannot corrupt the stack.

Every line goes through the full pipeline — lex, parse, elaborate, typecheck
with the specification's `infer`, then evaluate on the reference machine. The
typechecker is the one from `P01_Specification`, not a re-implementation.
