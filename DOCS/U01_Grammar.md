# U01 — Grammar

The surface syntax catcat accepts **today**, as a working reference. This
describes the implemented language, not the designed one: where the two differ,
that is called out rather than glossed. For the designed language see
[D05](../P00_Design/D05_Surface_Syntax_and_Macros.md).

> **Current as of commit `9a21cf0`.**
> Source of truth: [E01_Lexer.fst](../P03_Elaboration/E01_Lexer.fst) (lexing),
> [E03_Parser.fst](../P03_Elaboration/E03_Parser.fst) (grammar),
> [E02_Ast.fst](../P03_Elaboration/E02_Ast.fst) (the tree it produces),
> [E04_Elaborate.fst](../P03_Elaboration/E04_Elaborate.fst) (what elaborates),
> [E05_Locate.fst](../P03_Elaboration/E05_Locate.fst) (`locate`).
> If this file and those disagree, they are right. Re-check on any P03 change.

---

## 1. Grammar

```ebnf
program    = decl* ;

decl       = define | locate | expression ;

define     = "define" word "(" signature ")" "{" term* "}"
           | "define" word                   "{" term* "}" ;   (* inferred *)

locate     = "locate" word ;                                   (* see §5 *)

expression = term* ;

signature  = input* "--" output* ;
input      = "$" name ":" type | type ;
output     = type | "!" name ;

type       = "Box" "[" type "]"
           | "Rc"  "[" type "]"
           | "#" name
           | name ;

term       = integer
           | word
           | "$" name
           | conditional
           | "{" term* "}" ;

conditional = "if" block "then" block [ "else" block ] "endif" ;
block       = "{" term* "}" ;
```

The `conditional` production is written out here for readability, but it is not
built into the parser: it is one entry in a **macro table** (§5), and the parser
that reads it is generic over the table.

**`define` and `locate` are not reserved words.** Both are recognised by
*position* — first token of a declaration — so `define locate { 42 }` is legal
and `locate` inside a body is an ordinary word. The same rule leaves `then`,
`else` and `endif` free everywhere outside a conditional.

`if` is the one word that is effectively taken, and by the macro table rather
than by the grammar: `define if { 9 }` is accepted, but every later `if` is read
as the macro, so the definition can never be called. Nothing warns about this
yet.

`{ … }` parses as a term anywhere, but the only constructs that **consume** one
are `define` and the conditional of §4. A block appearing anywhere else is
rejected by the elaborator: general block consumers need macros or handlers,
and neither exists yet.

**An expression runs to the end of the input.** A `define` may be followed by
more declarations on the same line; an expression may not, because every
remaining token is read as part of it.

```
define a { 1 } define b { 2 } a b +     \ three declarations, fine
1 2 + define c { 3 }                    \ error: unknown word: define
```

This is a consequence of the no-lookahead rule (§6), not an oversight: nothing
marks where an expression ends, so it ends at the input.

---

## 2. Lexical structure

**Words are free-form.** Any run of characters that is neither whitespace nor
bracket punctuation is one word, so `+`, `<=`, `pop-all` and `hypot` are all
ordinary names. Arithmetic is spelled with operators — see
[U02](U02_Word_Reference.md).

**Self-delimiting punctuation:** `{ } ( ) [ ] :`. These end a word run with no
surrounding space needed, so `{dup *}` and `{ dup * }` are identical. This is
the deliberate divergence from Forth that makes precise tooling possible.

**`--` is NOT self-delimiting.** It is an ordinary space-separated word.

```
( i64 -- i64 )      \ correct
( i64--i64 )        \ error: one word named "i64--i64"
```

Everything inside a `( … )` is space-separated and the arrow is no exception.
Requiring the space is also what keeps the scanner lookahead-free (§6). As a
consequence `--` cannot be used as a user word name.

**Sigils**, recognised by first character, so the parser never needs to guess
which region of a signature it is in:

| Sigil | Meaning | Status |
|---|---|---|
| `$x` | local variable | works |
| `#T` | parametric type | parses, rejected by the elaborator |
| `!Eff` | effect | parses, **silently discarded** — see §7 |

**Integers** are an optional `-` followed by at least one digit. The digit
requirement is what lets `-` be a word:

```
10 3 -      \ subtraction   -> 7
10 -3 +     \ negative literal -> 7
```

**Comments** run from `\` to end of line. `( … )` is a *type annotation*, not a
comment — the one place this language reverses a Forth convention rather than
dropping it.

---

## 3. Signatures

Signatures read in the **Forth convention: bottom-to-top, top of stack on the
right.** `( a b -- c )` consumes `b` from the top. The core's index lists are
the opposite — head is top — and elaboration reverses them.

```
( i64 i64 -- i64 )              positional
( $x:i64 $y:i64 -- i64 )        named parameters
( -- i64 )                      no inputs
( Rc[i64] -- i64 )              pointer types
```

**Named parameters must be the topmost contiguous run** — a suffix, since the
top is on the right. `( $x:i64 i64 -- i64 )` is rejected. Binding pops from the
top, so a suffix is a straight run of pops; naming a buried parameter would
generate exactly the hidden stack traffic locals exist to remove.

**Reads consume.** A local read once compiles to a move; read twice or more it
is copied each time and so must be `Copy`; read zero times it is dropped, and so
must be `Drop`. A linear local left unconsumed is a type error, not a leak.
**A read inside a conditional branch always counts as repeated** (§4), whatever
the actual number.

### The signature is optional

`define sq { dup * }` infers `( i64 -- i64 )`. Writing a signature is an
assertion, checked against the body.

```
define sq   { dup * }        \ ( i64 -- i64 )
define pair { dup 1 + }      \ ( i64 -- i64 i64 )
define cmp  { < }            \ ( i64 i64 -- bool )
define bad  { dup }          \ rejected
```

`bad` is not an inference failure. The core is monomorphic, so a body whose
stack effect is genuinely polymorphic has no signature to infer; the error asks
for one to be written. Inference is a single left-to-right walk with no
constraint solver, because in a concatenative language composing programs *is*
composing signatures.

---

## 4. Conditionals

```
if { cond } then { conseq } endif
if { cond } then { conseq } else { alt } endif
```

The **condition block runs inline** and must leave a `bool` on top. It may be
empty when the condition is already computed:

```
define abs  { dup 0 < if { } then { 0 swap - } endif }        \ ( i64 -- i64 )
define sign { dup 0 < if { } then { pop -1 } else { pop 1 } endif }
```

**`endif` is mandatory; `else` is not.** The terminator is what keeps the
grammar free of an ε-branch, and that in turn is what lets `then`, `else` and
`endif` stay ordinary word names everywhere outside this construct — nothing is
reserved. See §6.

### What the branches must agree on

**The final stack state, not the way each branch is written.** Branches are
row-polymorphic, so one may reach beneath the condition where the other does
not:

```
define dec_if_big { dup 10 < if { } then { 1 - } endif }      \ ( i64 -- i64 )
```

`then` is `( -- )` and the implicit `else` is `( i64 -- i64 )`; framing the
first by `i64` makes both the same, so this is accepted. What is rejected is
disagreement on what is left behind:

```
catcat> define mismatch { dup 0 < if { } then { true } else { 1 } endif }
error: the branches of an if leave different types on the stack
```

**An omitted `else` is `else { }`.** So "the `then` branch must not change the
stack" is not a separate rule — it is what branch agreement says when the other
branch is empty.

**A local read inside a branch is compiled as a copy**, never a move, so its
type must be `Copy`. A move would consume the slot in one branch and not the
other, leaving the two with different stacks.

There is no `while` or recursion yet, so conditionals are the whole of control
flow.

---

## 5. Macros, and `locate`

### The macro table

`if` is not a parser built-in. It is one entry in `E03_Parser.macro_table`, and
a macro there is **a grammar production plus a term transformer**: a fixed run
of slots, then an alternation keyed on a word that is always consumed.

| Slot | Matches |
|---|---|
| `MsBlock` | `{ … }`, captured as its term list |
| `MsWord` | one identifier, captured as a string |
| `MsKeyword s` | the literal word `s`; consumed, captures nothing |

The whole table is checked to be LL(1) by `ll1_ok`, which requires that no two
macros share a leading word and no two alternatives of one macro share a key.
That check is run over the shipped table with `assert_norm`, not asserted in
prose — it is the seed of the verified CFG-to-recursive-descent generator §6
explains.

Two properties are deliberate and worth relying on:

- **A macro has no stack access.** Its input is syntax and its output is
  syntax, so nothing it does is visible at runtime.
- **A macro cannot consume the enclosing `}`.** Slots are parsed by the same
  functions the block parser uses, so a macro that runs out of tokens inside
  its production reports an error rather than reaching past the brace.

**User-defined macros do not exist yet.** The table is built in and `if` is its
only entry; registering a macro from catcat source is what the framework is for
and needs the elaboration-time interpreter.

### `locate`

```
locate <word>
```

Prints what a name is. There are three answers, and which one you get says
where the name lives:

```
catcat> locate +
+ ( i64 i64 -- i64 )
  \ primitive: integer add

catcat> locate if
macro if
  if { } then { } endif
  if { } then { } else { } endif

catcat> define abs { dup 0 < if { } then { 0 swap - } endif }
defined abs ( i64 -- i64 )
catcat> locate abs
define abs ( i64 -- i64 ) {
  dup 0 < if { } then { 0 swap - } else { } endif
}
```

A macro is reported before a word of the same name, because that is the order
the parser resolves in.

**The body shown is decompiled from the core term, not remembered source.**
Nothing keeps the text you typed. What comes back is therefore what the word
*is* after elaboration — note the `else { }` that `abs` never wrote — and it
**re-parses to the same term**, so the output can be pasted back.

Where the core has something the surface cannot spell, the rendering is
deliberately not valid syntax rather than a plausible-looking guess:

| Printed | Means |
|---|---|
| `pick.2` / `roll.2` | deep stack access two slots down — the compiled form of a `$x` local, whose name is gone |
| `#7` | a word id with no name in scope |
| `bool>sum`, `case { … } { … }` | a `TCase` that is not the two-branch boolean shape `if` reconstructs |

So `locate hypotsq` shows the locals gone:

```
catcat> define hypotsq ( $x:i64 $y:i64 -- i64 ) { $x $x * $y $y * + }
catcat> locate hypotsq
define hypotsq ( i64 i64 -- i64 ) {
  pick.1 pick.2 * pick.1 pick.2 * + roll.1 pop roll.1 pop
}
```

which is the clearest available demonstration of what §3's "reads consume"
paragraph actually compiles to.

---

## 6. No lookahead

A hard constraint on the grammar, not a property of the current parser: **the
lexer is a plain DFA and the parser is LL(1).** Every decision is made on the
single character or token in hand.

The binding reason is a planned standard-library feature — verified conversion
of a left-recursion-free CFG into a recursive-descent parser. A language whose
own grammar needed lookahead could not be described by the tool it ships. Speed
is the secondary reason: no buffer, no backtracking, so incremental reparsing
for the language server stays local.

Any syntax proposal needing a second token to disambiguate is rejected on these
grounds. This is what settled the `--` question in §2, and it is why `endif` is
mandatory in §4.

To be precise about what "no lookahead" forbids, since the two are easy to
confuse: LL(1) *permits* dispatching on the token in hand without consuming it,
which the parser already does when it decides whether a signature slot is a
type or a `$name`. What is forbidden is needing a **second** token. An optional
trailing `else` would need one — after `if { c } then { t }`, a following word
could be the `else` of this conditional or an ordinary word after it, and only
the token after that could tell. Requiring `endif` means every alternation
point consumes a keyword instead.

---

## 7. Not yet implemented

Each is specified in [D05](../P00_Design/D05_Surface_Syntax_and_Macros.md) and
absent from the implementation. Listed because the gap between the two documents
is otherwise invisible.

| Feature | State |
|---|---|
| `!Eff` in a signature | parses, then **silently dropped**; `( -- i64 !IO )` records `( -- i64 )` |
| loops, recursion | not parsed — `if` is the whole of control flow |
| `#T` generics | parses, elaborator rejects |
| `let` and `let (…)` | not parsed |
| effects, handlers | not parsed |
| sums, classes, `module`, `::`, `.` | not parsed |
| strings `"…"`, quotation `'…'`, backtick | not lexed |
| user-defined macros | the framework exists (§5); the table is built in and only the compiler can add to it |
| `Box`/`Rc` construction | types exist; no surface word builds one |
| source positions in errors | absent — errors are messages without spans |

The effect row being **silently discarded** is the one that can mislead: the
signature is accepted and the effect vanishes without a warning. It is a
placeholder for the D03 pass, not a design decision.
