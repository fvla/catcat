# D05 — Surface Syntax, Locals, Modules, and Macros

The core calculus (D02) has no locals, no generics, no namespaces and no macros.
This document specifies the surface language and how it elaborates away.

Design stance, from the draft and kept: **minimal syntax, but not free-form.**
Forth's total syntactic freedom defeats tooling, and a fast, precise language
server is a stated goal. So the bracket vocabulary is fixed and small, and
extension happens through macros with declared effects rather than through
arbitrary reader hacks.

---

## 1. Lexical vocabulary

| Form | Meaning |
|---|---|
| `{ … }` | Code block. Executed directly, or consumed by a macro. |
| `( … )` | Deferred-parse block. Type annotations are the main use — **not comments**. |
| `[ … ]` | Generic instantiation: `SIMD[f64]`, `Counter[#T]`. |
| `#T` | Parametric type variable. |
| `!Eff` | Effect. |
| `$x` | Local variable. Bound by a named parameter or `let` (§3). |
| `$*x` | Dynamically-scoped variable (Raku-style). |
| `let` | Binds block outputs to names; `let (…)` destructures (§3.3). |
| `"…"` | String literal. |
| `'…'` | Reserved — Lisp-style quotation. See §6. |
| `` `…` `` | Reserved, unassigned. |
| `::` | Namespace separator, word-internal: `math::sqrt`. |
| `.` | Member access on classes and effects: `counter.increment`. |
| `--` | Separates inputs from outputs inside `( … )`. |

**Deliberately absent:** `;`. `{}` delimits definitions, so Forth's terminator has
no job. Also absent: terse Forth names like `@` and `."`. Words are not limited
to 5–8 characters and should not read as though they were; `dup`, `swap`, `pop`,
`rot` stay because they are genuinely idiomatic, but `fetch` beats `@`.

**Sigil rule:** the first character after a sigil should be alphanumeric. This
keeps `$x`/`$*x` unambiguous and leaves room for future sigil prefixes without
retrofitting the lexer.

**Whitespace rule:** unlike Forth, brackets and quoting symbols are *not* words
and do **not** require surrounding spaces. `{hypot dup *}` and `{ hypot dup * }`
lex identically. The lexer treats `{ } ( ) [ ] :` — **and `--`** — as
self-delimiting punctuation, so word boundaries fall around them automatically.

> `--` was added to that set after building the lexer. With only brackets
> self-delimiting, `( i64--i64 )` lexed `i64--i64` as a single word and a
> tightly-written signature failed to parse, while `{$x $x mul}` worked — a
> surprising asymmetry, since both are structural punctuation. A *single* `-` is
> unaffected, so `-5` still lexes as an integer literal and `pop-all` as one
> word. See D-28.

This is a real divergence from Forth rather than a cosmetic one: in Forth the
absence of such punctuation is what allows the reader to be redefined at will,
and giving that up is the price of the fixed vocabulary that makes precise
tooling possible.

---

## 2. Signatures

```
( i64 i64 -- f64 !IO !Alloc )
( $x:f64 $y:f64 -- f64 )          -- named parameters, §3.1
( -- #T )
( #T -- #T i64 )
( #R i64 i64 -- #R f64 !IO )      -- explicit row variable, rarely needed
```

Effects live inside the parentheses, each with its own `!` sigil. The sigil makes
effects lexically distinguishable from types, so the parser never needs lookahead
to know which region it is in — which matters for incremental reparsing.

The row variable is implicit and almost never written. `#R` names it explicitly
in the rare case a signature must relate two rows.

> **Stack order.** Surface signatures follow the Forth convention: written
> bottom-to-top, with the **top of the stack on the right**. So `( a b -- c )`
> consumes `b` from the top. The core's index lists are the opposite — head is
> top (D02 §2) — and elaboration reverses them.
>
> This mismatch is intentional, because `( a b -- c )` is what a Forth
> programmer expects to read. It is also exactly the kind of detail that
> produces silent bugs: the abandoned draft compared stacks from the head while
> appending residuals at the tail, and the resulting confusion is visible in its
> `compose_stack_functions`. State the convention at every boundary.

---

## 3. Locals

Purpose, per the draft: hiding stack manipulation where shuffling would obscure
intent.

### 3.1 Named parameters

Inputs are named **in the signature**, not bound by a separate form in the body:

```
define hypot ( $x:f64 $y:f64 -- f64 ) {
    $x $x * $y $y * + sqrt
}
```

The signature is the single place a reader looks to learn both the shape and the
names. Outputs stay positional types — naming them would suggest a relation
between input and output names that the type system does not track.

### 3.2 Mixing named and unnamed inputs

Permitted, with one restriction: **named parameters must occupy the topmost
contiguous run** — a suffix in surface notation, since the top of the stack is
on the right (§2).

```
( i64 $x:f64 $y:f64 -- f64 )      -- legal: names the top two
( $x:f64 i64 -- f64 )             -- rejected
```

The reason is mechanical rather than stylistic. Binding pops from the top, so a
suffix elaborates to a straight run of pops. Naming a parameter buried under
unnamed ones would require shuffling the unnamed values out of the way and back
— generating exactly the hidden stack traffic locals exist to remove, and
silently changing where the unnamed slots end up. The restriction keeps the
residual stack shape obvious by inspection.

The rejection should suggest the fix: reorder the signature, or name the
intervening parameters too.

### 3.3 `let`

```
let $z = { $x $x * $y $y * + }
let ($a $b) = { divmod }
let $w:f64 = { … }                -- annotation optional, inferred otherwise
```

`let` runs the block and binds its outputs. The block's output arity must match
the number of names; a mismatch is an arity error, not a silent truncation.

**Destructuring order follows §2's convention**: in `let ($a $b) = { … }`, `$b`
is the top of the block's output. This mirrors signatures exactly, so the two
places a reader sees a name list agree. Stated explicitly because a reversed
reading here would be a quiet, plausible-looking bug.

Parenthesising the binding list is consistent with the general rule for `()`
(§1): a region that does not use the default lexer/parser. A binding list is one
such region, so this is not a third meaning for the bracket.

### 3.4 Semantics

**Locals are elaborated entirely into stack shuffles.** The core never learns
they existed — no environment in any semantic rule, no frame, no runtime notion
of a local. "Program = pure composition" (D02 §8) stays literally true.

**Binding consumes.** Each subsequent read is a *move* unless the type is
`Copy`. In `hypot` above, `$x` is read twice, which is fine precisely because
`f64` is `Copy`. Reading a non-`Copy` local twice is a type error, exactly as
using a moved value twice would be.

**How the elaborator decides** ([E04_Elaborate.fst](../P03_Elaboration/E04_Elaborate.fst)).
It counts occurrences of each name up front, which is what avoids needing a
liveness analysis:

| Reads | Compiles to | Cleanup |
|---|---|---|
| exactly one | `roll` — a move, consuming the slot | none needed |
| two or more | `pick` each time (so the type must be `Copy`) | slot dropped at end of body |
| none | — | slot dropped at end of body |

Dropping requires `Drop`, so a linear local that is never consumed is a type
error rather than a silent leak — which is the point of D-08. Note the
single-read case compiles to a *move*, so the common `( $x:i64 -- i64 ) { $x }`
costs one `roll` and nothing else.

This is what makes locals usable for linear resources — the case where hiding
stack juggling helps most. A by-copy reading would have required `Copy` on every
bound type and been useless for exactly the `Counter` of D03 §3.

Scoping is lexical, to the enclosing `{}`.

---

## 4. Modules and namespacing

Modules are Dictionary handlers (D04 §2). `use` pushes a static frame; `::` is
lookup in the chain.

```
module math {
    export define sqrt ( f64 -- f64 ) { … }
}

use math
… math::sqrt …
… sqrt …            -- unqualified, resolved through the ambient chain
```

Because a module is an interface plus an implementation, swapping one for another
is pushing a frame — the SIMD-functor case of D04 §3. There is no second
name-resolution mechanism; module lookup and Dictionary lookup are the same walk.

`.` is member access on class instances and effects: `counter.increment`. It
differs from `::` in that the left side is a *value* (or an effect in scope),
whereas `::` takes a namespace.

---

## 5. Macros

A macro consumes words to its right at parse time and produces terms.

**Macros are not variadic.** Following the draft's instinct: a macro declares how
many words it consumes, via an effect annotation, rather than scanning until a
terminator. This keeps the parser predictable and incremental — an LSP can
reparse a region without re-running arbitrary reader code.

```
macro define ( -- ) !Parse[consume 2] { … }
```

Macro effects are ordinary effects in the `Parse` family (D03 §7), statically
staged. So a macro's impact on the lexer/parser pipeline is *in its signature*,
which is what makes tooling able to reason about it.

`{}` blocks are the macro's raw material: a macro receives a block as code and
may reinterpret it under different rules. This is the "consumed by a macro" half
of D01 §3.2 — and note that a block is never a runtime value, so a macro
consuming one is an elaboration-time operation with no runtime residue.

---

## 6. Reserved and undecided

- **`'…'`** — reserved for Lisp-style quotation. The natural fit in a language
  where code is first-class at elaboration time but functions are not: `'word`
  would be code-quoting a single word, i.e. `{ word }` without the braces.
  Recommended, not yet committed.
- **`` `…` ``** — reserved, no assigned meaning. Leaving one bracket pair
  unassigned is cheap insurance.
- **`::` vs `:`** — `::` recommended, matching Rust and leaving `:` free for
  type ascription should it be wanted.

---

## 7. Elaboration order

```
source
  -> lex                        (fixed vocabulary, §1)
  -> parse                      (macros run here, !Parse effects, §5)
  -> resolve names              (Dictionary chain: modules, interfaces, §4)
  -> elaborate                  (locals -> shuffles §3; generics -> monomorphic)
  -> core term                  (M05_Terms)
  -> typecheck                  (M06_Typing; inference = composition)
  -> specialize                 (M11; static effects erased, D04 §4)
  -> IR -> backend
```

Everything above `core term` is P03 and is not specified in P01. The important
property is that the boundary is sharp: the core is small enough to prove things
about precisely because generics, locals, namespaces and macros are all gone by
the time a program reaches it.
