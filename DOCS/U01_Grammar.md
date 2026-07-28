# U01 — Grammar

The surface syntax catcat accepts **today**, as a working reference. This
describes the implemented language, not the designed one: where the two differ,
that is called out rather than glossed. For the designed language see
[D05](../P00_Design/D05_Surface_Syntax_and_Macros.md).

> **Current as of commit `692cbe9`.**
> Source of truth: [E01_Lexer.fst](../P03_Elaboration/E01_Lexer.fst) (lexing),
> [E03_Parser.fst](../P03_Elaboration/E03_Parser.fst) (grammar),
> [E02_Ast.fst](../P03_Elaboration/E02_Ast.fst) (the tree it produces),
> [E04_Elaborate.fst](../P03_Elaboration/E04_Elaborate.fst) (what elaborates).
> If this file and those disagree, they are right. Re-check on any P03 change.

---

## 1. Grammar

```ebnf
program    = decl* ;

decl       = define | expression ;

define     = "define" word "(" signature ")" "{" term* "}"
           | "define" word                   "{" term* "}" ;   (* inferred *)

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
           | "{" term* "}" ;
```

`{ … }` parses as a term anywhere but is **rejected by the elaborator** outside
a definition body — blocks need macros or handlers to consume them, and neither
exists yet.

**An expression runs to the end of the input.** A `define` may be followed by
more declarations on the same line; an expression may not, because every
remaining token is read as part of it.

```
define a { 1 } define b { 2 } a b +     \ three declarations, fine
1 2 + define c { 3 }                    \ error: unknown word: define
```

This is a consequence of the no-lookahead rule (§4), not an oversight: nothing
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
Requiring the space is also what keeps the scanner lookahead-free (§4). As a
consequence `--` cannot be used as a user word name.

**Sigils**, recognised by first character, so the parser never needs to guess
which region of a signature it is in:

| Sigil | Meaning | Status |
|---|---|---|
| `$x` | local variable | works |
| `#T` | parametric type | parses, rejected by the elaborator |
| `!Eff` | effect | parses, **silently discarded** — see §5 |

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

## 4. No lookahead

A hard constraint on the grammar, not a property of the current parser: **the
lexer is a plain DFA and the parser is LL(1).** Every decision is made on the
single character or token in hand.

The binding reason is a planned standard-library feature — verified conversion
of a left-recursion-free CFG into a recursive-descent parser. A language whose
own grammar needed lookahead could not be described by the tool it ships. Speed
is the secondary reason: no buffer, no backtracking, so incremental reparsing
for the language server stays local.

Any syntax proposal needing a second token to disambiguate is rejected on these
grounds. This is what settled the `--` question in §2.

---

## 5. Not yet implemented

Each is specified in [D05](../P00_Design/D05_Surface_Syntax_and_Macros.md) and
absent from the implementation. Listed because the gap between the two documents
is otherwise invisible.

| Feature | State |
|---|---|
| `true` / `false` literals | **absent** — booleans only arise from `<`, `<=`, `=` |
| `!Eff` in a signature | parses, then **silently dropped**; `( -- i64 !IO )` records `( -- i64 )` |
| `#T` generics | parses, elaborator rejects |
| `let` and `let (…)` | not parsed |
| effects, handlers | not parsed |
| sums, classes, `module`, `::`, `.` | not parsed |
| strings `"…"`, quotation `'…'`, backtick | not lexed |
| macros | not parsed |
| `Box`/`Rc` construction | types exist; no surface word builds one |
| source positions in errors | absent — errors are messages without spans |

The effect row being **silently discarded** is the one that can mislead: the
signature is accepted and the effect vanishes without a warning. It is a
placeholder for the D03 pass, not a design decision.
