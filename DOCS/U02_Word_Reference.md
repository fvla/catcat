# U02 — Word Reference

Every word the language provides today. That is a short list: fifteen
primitives, two constants, two IO operations, one abort, and three stack
shuffles.

> **Current as of commit `018e75a`.**
> Source of truth:
> [E06_Repl.fst](../P03_Elaboration/E06_Repl.fst) `prelude_nenv` (names and
> signatures), [R03_Prelude.fst](../P02_Reference/R03_Prelude.fst) (word ids and
> the dictionary), [R02_Machine.fst](../P02_Reference/R02_Machine.fst)
> `apply_prim` (semantics), [E05_Locate.fst](../P03_Elaboration/E05_Locate.fst)
> (`locate`), [E04_Elaborate.fst](../P03_Elaboration/E04_Elaborate.fst)
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
| `str` | immutable string; `"…"` literals, see §7 |
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
the start of a declaration, and so are `effect`, `extern`, `macro` and
`locate`. `then`,
`else`, `endif`, `over`, `init`, `declare`, `alt` and `end` are likewise free —
each is a keyword only inside the construct that introduces it. Five names are
effectively taken — `if`, `unsafe`, `try`, `handle` and `with` — because they
are dispatched on wherever a term may start: a definition of one is accepted but
can never be called ([U01](U01_Grammar.md) §1). `recurse` is a sixth inside any
signed `define`, where it names the word being defined. **Declaring a macro adds a name to that
list**, silently.

Grammar, locals, and the inference rules are in [U01](U01_Grammar.md).

---

## 7. Strings and IO

| Word | Signature | Meaning |
|---|---|---|
| `show` | `( i64 -- str )` | render a number |
| `parse` | `( str -- i64 )` | read a number; `0` if malformed |
| `cat` | `( str str -- str )` | concatenate, `below` then `top` |
| `str=` | `( str str -- bool )` | equality |
| `print` | `( str -- !IO )` | write the string, **no newline added** |
| `read` | `( -- str !IO )` | read a line, newline stripped |

Literals are double-quoted and may span lines — see [U01](U01_Grammar.md) §2 for
the escapes.

```
catcat> "a" "b" cat
ok  "ab"
catcat> "answer: " 42 show cat "\n" cat print
answer: 42
catcat> echo 5 | catcat.exe 'read parse dup * show print'
25
```

`str=` is spelled separately from `=` because the core is monomorphic: `=` is
`i64` equality and nothing overloads it. A single `=` over both is an interface,
which is a real feature and not a second prelude entry.

`str` is `Copy` and `Drop` like every other primitive, so it duplicates and
discards freely. That is right for an immutable value and it does commit the
eventual implementation to sharing rather than to owned buffers — an owned
buffer would be `Box`-like and therefore linear.

The first four are primitives; `print` and `read` are **operations of the
built-in `IO` effect**, and `locate` says which is which:

```
catcat> locate cat
cat ( str str -- str )
  \ primitive: string concatenation
catcat> locate print
print ( str -- !IO )
  \ operation of effect IO
```

Nothing in the effect system is special-cased for them; the only asymmetry is
over who may DECLARE one: the interpreter owns effects 0–5 and `effect` allocates
from 6 upward, so no program can declare another host-serviced effect. The block
is listed in [U01](U01_Grammar.md) §6.

`IO` is nevertheless an effect like any other and can be intercepted with
`handle` — see [U01](U01_Grammar.md) §6, which also covers declaring effects,
writing handlers, and what `!IO` in a signature now means.

**`parse` yields `0` on anything it cannot read**, and `read` yields `""` at end
of input. Both are placeholders for the same missing thing: the honest signature
is `( str -- option[i64] )`, which needs sums to have surface syntax. A sentinel
is preferred to a stuck machine, because a stuck machine loses the session.

---

## 7a. C functions

`extern` declares a libc function; see [U01](U01_Grammar.md) §6 for the syntax,
the `!C !Unsafe` row and how to mock one. These are the symbols the REPL is
linked against today:

| Symbol | Signature | Notes |
|---|---|---|
| `strlen` | `( str -- i64 )` | |
| `puts` | `( str -- i64 )` | writes the string **and a newline**, unlike `print` |
| `abs` | `( i64 -- i64 )` | C `int`, so it truncates outside 32 bits |
| `time` | `( -- i64 )` | seconds since the epoch |
| `getpid` | `( -- i64 )` | |
| `getenv` | `( str -- str )` | `""` when unset — no option type yet |

```
catcat> extern strlen ( str -- i64 )
extern strlen ( str -- i64 !C !Unsafe )
catcat> "hello, world" strlen
ok  12
```

You still write the `extern` yourself: the table above is what the *host* can
service, not a set of predeclared words. A name outside it declares fine and
fails at the call, reported as an operation that escaped — which is exactly what
it is.

---

## 7b. Failure

| Word | Signature | Meaning |
|---|---|---|
| `fail` | `( -- !Fail )` | abandon the enclosing `try` block |

`fail` is the only operation of the `Fail` effect. `try { … } catch { … }` is
what catches it and discharges `!Fail` from the row; the syntax, the rules the
two blocks must satisfy and the two current limits are in
[U01](U01_Grammar.md) §6.

```
catcat> try { fail "boom" } catch { "recovered" }
ok  "recovered"
catcat> fail
unhandled: fail escaped with no handler in scope
```

Everything the try block built is discarded before `catch` runs, so `catch`
takes no inputs and must leave the same stack the try block would have.

This is what `parse` and `getenv` want and cannot yet use. Their honest
signatures are `( str -- i64 !Fail )` and `( str -- str !Fail )`, and the reason
they still return sentinels is not that failure is unavailable — it is that a
caller who *wants* the sentinel would have no way to ask for it back. That needs
`catch` to receive the error, which needs generics.

---

## 8. Inspecting: `locate`

```
locate <word>
```

Forth's `LOCATE`/`SEE`. Prints a primitive's description, a macro's production
and templates, or a definition's body — the last **decompiled from the core
term**, so it shows what the word is after elaboration rather than what was
typed.

```
catcat> locate <=
<= ( i64 i64 -- bool )
  \ primitive: integer less-or-equal
```

Like `define`, `locate` is recognised by position and reserves nothing. Full
description, including how deep stack access and unnamed ids are rendered, is in
[U01](U01_Grammar.md) §5.

---

## 9. The REPL

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
`(empty)`.

Every line is lexed whole and then parsed **one declaration at a time**,
evaluating as it goes, because a `macro` declaration changes the grammar the
rest of the line is read with ([U01](U01_Grammar.md) §5). Each declaration goes
through the full pipeline — parse, elaborate, typecheck with the
specification's `infer`, then evaluate on the reference machine. The typechecker
is the one from `P01_Specification`, not a re-implementation.

**A lexing error leaves the session untouched.** A parse or type error leaves it
as of the last declaration that succeeded — so on a line holding several
declarations, the ones before the error have run. A type error still costs
nothing on its own declaration, which is what keeps a mistyped expression from
corrupting the stack:

```
catcat> 1 2 +
ok  3
catcat> pop pop
error: pop: the stack is empty
catcat> 2 3 +
ok  3 5
```

The failed line left the `3` exactly where it was.
