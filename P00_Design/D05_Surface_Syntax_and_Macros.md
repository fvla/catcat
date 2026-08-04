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

**Word names are free-form.** Any run of characters that are neither whitespace
nor bracket punctuation is a word, so **the arithmetic and comparison words are
operators**: `+ - * / %` and `< <= =`, not `add`, `mul`, `lt`. The rule against
terse names is about *unreadable* abbreviations, and `+` is not one of those —
it is the most widely understood name a word can have.

Two consequences of the lexer's rules, both intended:

- `-` is a word but `-3` is a literal, because an integer needs at least one
  digit after the sign. `3 - 4` subtracts; `3 -4 +` pushes a negative.
- `!=` is unavailable, since `!` opens an effect sigil and so cannot begin a
  word. Use `= not`, or name it.

**Sigil rule:** the first character after a sigil should be alphanumeric. This
keeps `$x`/`$*x` unambiguous and leaves room for future sigil prefixes without
retrofitting the lexer.

**Whitespace rule:** unlike Forth, brackets and quoting symbols are *not* words
and do **not** require surrounding spaces. `{hypot dup *}` and `{ hypot dup * }`
lex identically. The lexer treats `{ } ( ) [ ] :` as self-delimiting
punctuation, so word boundaries fall around them automatically.

**`--` is an ordinary space-separated word** and is *not* in that set. Write
`( i64 -- i64 )`; `( i64--i64 )` is one word and an error. This is consistent —
everything inside a `( … )` is space-separated, and the arrow is no exception —
and it is what keeps the scanner lookahead-free (§1.1). D-28 briefly went the
other way and was reverted.

This is a real divergence from Forth rather than a cosmetic one: in Forth the
absence of such punctuation is what allows the reader to be redefined at will,
and giving that up is the price of the fixed vocabulary that makes precise
tooling possible.

### 1.1 No lookahead, in the lexer or the parser

A hard constraint, not an aspiration (D-30): **lexing and parsing each decide on
the token in hand and never peek further.** The scanner is a plain DFA — every
branch is a predicate on one character — and the parser is LL(1).

Two reasons this is worth designing around rather than discovering later:

- **Speed**, which is the stated motivation. A lookahead-free scanner needs no
  buffer, no backtracking, and no restart, so incremental reparsing for the
  language server is a local operation.
- **It is the precondition for a planned standard-library feature**: verified
  conversion of a left-recursion-free context-free grammar into a
  recursive-descent parser. A language whose own grammar needs lookahead could
  not be described by the tool it ships.

This constraint is what settles the `--` question above. Making the arrow
self-delimiting required the scanner to look at a *second* character to
distinguish `--` from `-3` and from `pop-all` — the only lookahead anywhere in
the lexer, introduced for one piece of punctuation. Requiring the space costs a
keystroke and removes the exception.

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

### 2.1 Signatures are inferred

**The signature is optional. `define sq { dup * }` infers `( i64 -- i64 )`.**
Writing one is an assertion, checked against what the body actually does.

This is nearly free in a concatenative language, and worth understanding why,
because it is a genuine structural payoff rather than an implementation trick.
Composition of programs *is* composition of signatures (M03), so inference is a
single left-to-right walk with no constraint graph, no generalisation step, and
no Hindley–Milner machinery. The algorithm is: model the stack; when the model
runs dry, the body must be consuming another input, so invent a variable and
record it. The variables invented, in order, are the inputs. Every word's
signature is ground, so the only constraint that ever arises is
`variable := concrete type` — the substitution is a flat map, and there is no
unifier, no occurs check, and no union-find anywhere in it.

**What inference cannot do, and why that is correct.** A body whose stack effect
is genuinely polymorphic leaves a variable unconstrained:

```
define sq   { dup * }        -- ( i64 -- i64 )
define pair { dup 1 + }      -- ( i64 -- i64 i64 )
define cmp  { < }            -- ( i64 i64 -- bool )
define bad  { dup }          -- rejected: nothing constrains the type
```

`bad` is not an inference failure. The core is monomorphic (D02 §5), so there is
no signature to infer — the error asks for one to be written. When generics
land, this is the point that changes.

**Where signatures stay mandatory: inside an effect declaration.** An interface
exists to fix signatures *before* any implementation, so there is nothing to
infer from and inferring would invert the dependency. **Now enforced**: see
§3.5, where `declare` without a signature is an error.

**This is the input to the tooling story.** A stack language's central
readability problem is that a word's effect on the stack is invisible at the
call site. Since the checker computes that effect for every word whether or not
it is written down, the language server can display it inline — the signature is
always available, never stale, and costs nothing to keep. See N02 Q-11.

---

## 2.2 Conditionals

```
if { cond } then { conseq } endif
if { cond } then { conseq } else { alt } endif
```

The condition block runs inline and must leave a `bool`. It may be empty, when
the condition has already been computed by preceding words.

**`endif` is mandatory** (D-34). The reason is §1.1: with an optional trailing
`else`, deciding whether a word following `if { c } then { t }` is this
conditional's `else` or an ordinary word after it needs a *second* token.
Requiring the terminator means every alternation point consumes a keyword, so
the grammar has no ε-branch and `then`/`else`/`endif` stay legal word names
everywhere outside the construct — nothing is reserved, consistent with the
free-form words of §1.

**Branches agree on the final stack state**, not on how each is written; the
rule is `M03.srow_join` and D02 §5 explains it. An omitted `else` is `else { }`,
so "the `then` branch must not change the stack" is a consequence rather than a
separate rule.

This is currently hardcoded in the parser. It is the production the macro
system of §5 has to be able to express, and it moves into that table once the
table exists — `if` is meant to be a macro, not syntax.

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

## 3.5 Effects, handlers and rebinding — as implemented

The syntax that runs today. It is narrower than §4's module story and reaches
the same machinery, so it is recorded here rather than left to be inferred from
the difference.

```
effect Counter {
    declare tick  ( -- i64 )
    declare reset ( -- )
}

handle Counter over ( i64 ) init { 0 } {
    tick  { dup 1 + }        \ ( state -- i64 state )
    reset { pop 0 }          \ ( state -- state )
} { tick tick + }

with { noisy quiet } { noisy noisy }
```

Four things about it are decisions rather than defaults:

- **`declare` requires a signature** (above). This is the carve-out being
  enforced for the first time.
- **A handler is a stateful object, not a continuation consumer** (D-36). The
  state segment is `over ( … )`, the initialiser is `init { … }`, and each
  implementation is checked at the operation's signature with the state framed
  **on top** (D-46) — so `( args… state -- results… state )`. The state is the
  receiver, and a receiver is pushed last.
- **On exit the final state is left on the stack** (D-47). The handler *is* the
  object, so the object outlives the block.
- **`with` is static** (D-50). The rebinding is discharged during elaboration
  and leaves nothing in the core term — `M11`'s E3 demonstrated rather than
  assumed. The replacement must have the same signature; its effects may differ,
  which is the point.

`effect` and `handle` are parser built-ins rather than macro-table entries
(D-38): a block of `op { … }` pairs is not a term list, and the slot vocabulary
of §5 should not be stretched to cover it before it has been exercised on the
constructs it already fits.

Not yet reached from here: `use`, `::`, `.`, `module`, and the dynamic form of
`with`. §4's module system is the same Dictionary walk, so it is an extension of
this rather than a second mechanism.

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

### 5.1 What is implemented, and how far it is from the above

`macro` is a declaration and macros are user-definable today, but in a **strictly
weaker form than this section describes**, and the difference is worth being
exact about because the weaker form turned out to need nothing at all.

```
macro name ( slots ) { template }

macro name ( slots )
  alt key ( slots ) { template }
  alt key ( slots ) { template }
end
```

Slots are `{ $x }` for a block, `$x` for a word, and a bare word for a consumed
keyword. `DOCS/U01` §5 is the reference for the running form.

Three differences from the design above:

1. **The expansion is a TEMPLATE, not a program.** There is no `Parse` effect, no
   elaboration-time interpreter, and nothing a macro can compute — it substitutes
   captures into surface terms. `macro define ( -- ) !Parse[consume 2] { … }`
   remains the target and remains unbuilt.
2. **How much a macro consumes is in its PRODUCTION, not in an effect
   annotation.** The instinct the design records — declare consumption rather
   than scan to a terminator — survives intact and is what keeps the grammar
   LL(1); only its spelling differs. `ll1_extend` decides the property before
   accepting a production, so a session's grammar is LL(1) at every point.
3. **Nothing is hygienic.** A `$x` in a template naming no slot is an ordinary
   local read in whatever encloses the expansion.

The target shape the language is aiming at is different again, and neither this
section nor the implementation reaches it: a macro should be **an ordinary word
with an effect that lets it consume and transform code**, distinguished from a
normal word only in that resolution of its signature is deferred until after it
runs — Forth's `IMMEDIATE`, given a type. That is what the `Parse` family exists
for, and it is the reason the template form is deliberately not being extended.

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
