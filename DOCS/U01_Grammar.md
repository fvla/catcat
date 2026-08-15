# U01 — Grammar

The surface syntax catcat accepts **today**, as a working reference. This
describes the implemented language, not the designed one: where the two differ,
that is called out rather than glossed. For the designed language see
[D05](../P00_Design/D05_Surface_Syntax_and_Macros.md).

> **Current as of commit `fde16b1`.**
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

decl       = define | effect | extern | macro | locate | expression ;

define     = "define" word [ tparams ] "(" signature ")" "{" term* "}"
           | "define" word                        "{" term* "}" ;  (* inferred *)
tparams    = "[" ( "#" name )+ "]" ;                           (* see §3 *)

effect     = "effect" word "{" declare* "}" ;                  (* see §6 *)
declare    = "declare" word "(" signature ")" ;
extern     = "extern" word "(" signature ")" ;                 (* see §6 *)

macro      = "macro" word "(" mslot* ")" "{" term* "}"          (* see §5 *)
           | "macro" word "(" mslot* ")" malt+ "end" ;
malt       = "alt" word "(" mslot* ")" "{" term* "}" ;
mslot      = "{" "$" name "}" | "$" name | word ;

locate     = "locate" word ;                                   (* see §5 *)

expression = term* ;

signature  = input* "--" output* ;
input      = "$" name ":" type | type ;
output     = type | "!" name | "!" ;          (* bare ! : no effects, §3 *)

type       = "Box" "[" type "]"
           | "Rc"  "[" type "]"
           | "#" name
           | name ;

term       = integer
           | string
           | word
           | "$" name
           | conditional
           | try
           | handle
           | with
           | "{" term* "}" ;

conditional = "if" block "then" block [ "else" block ] "endif" ;
try         = "try" block "catch" block ;

handle      = "handle" word "over" "(" type* ")"                (* see §6 *)
              "init" block "{" impl* "}" block ;
impl        = word block ;

with        = "with" "{" rebind* "}" block ;                    (* see §7 *)
rebind      = word word ;

block       = "{" term* "}" ;
```

The `conditional` production is written out here for readability, but it is not
built into the parser: it is one entry in a **macro table** (§5), and the parser
that reads it is generic over the table. The table grows: `macro` adds to it.

**`define`, `effect`, `extern`, `macro` and `locate` are not reserved words.**
All five are recognised by *position* — first token of a declaration — so
`define locate { 42 }` is legal and `locate` inside a body is an ordinary word. The same rule
leaves `then`, `else`, `endif`, `over`, `init`, `declare`, `alt` and `end` free
everywhere outside the construct that introduces them. What position-recognition
does cost is the first slot of a declaration:

```
catcat> define macro { 7 }
defined macro ( -- i64 )
catcat> macro
error: expected a name after 'macro'
```

The word exists and is callable inside a body; it is only unreachable as the
first token of a declaration.

**Five words are effectively taken**, not by the grammar but by being dispatched
on wherever a term may start: `if`, `unsafe` and `try` (all three macro-table
entries), `handle` and `with`. Each is still *definable* — `define if { 9 }` is accepted —
but every later use is read as the construct, so the definition can never be
called.

Nothing warns about any of this. **Every macro declared adds a word to that
list**, which is the real cost of the macro system and is not diagnosed.

`recurse` is a sixth taken name, by a different route: inside a `define` with a
written signature it is bound to the word being defined (§6), shadowing any
other binding of that name for the length of the body.

`{ … }` parses as a term anywhere, but the only constructs that **consume** one
are `define`, the conditional of §4, the handler and rebinding forms of §6 and
§7, and any block slot a macro declares. A block appearing anywhere else is
rejected by the elaborator.

**An expression runs to the end of the input.** A `define` may be followed by
more declarations on the same line; an expression may not, because every
remaining token is read as part of it.

```
define a { 1 } define b { 2 } a b +     \ three declarations, fine
1 2 + define c { 3 }                    \ error: unknown word: define
```

This is a consequence of the no-lookahead rule (§8), not an oversight: nothing
marks where an expression ends, so it ends at the input.

---

## 2. Lexical structure

**Words are free-form.** Any run of characters that is neither whitespace nor
bracket punctuation is one word, so `+`, `<=`, `pop-all` and `hypot` are all
ordinary names. Arithmetic is spelled with operators — see
[U02](U02_Word_Reference.md).

**Self-delimiting punctuation:** `{ } ( ) [ ] : "`. These end a word run with no
surrounding space needed, so `{dup *}` and `{ dup * }` are identical. This is
the deliberate divergence from Forth that makes precise tooling possible.

**`--` is NOT self-delimiting.** It is an ordinary space-separated word.

```
( i64 -- i64 )      \ correct
( i64--i64 )        \ error: one word named "i64--i64"
```

Everything inside a `( … )` is space-separated and the arrow is no exception.
Requiring the space is also what keeps the scanner lookahead-free (§8). As a
consequence `--` cannot be used as a user word name.

**Sigils**, recognised by first character, so the parser never needs to guess
which region of a signature it is in:

| Sigil | Meaning | Status |
|---|---|---|
| `$x` | local variable | works |
| `#T` | parametric type | works — declared in `[…]`, matched at the call (§3) |
| `!Eff` | effect | works — resolved and checked (§6) |
| `!` | asserted-empty effect row | works (§3) |

**Integers** are an optional `-` followed by at least one digit. The digit
requirement is what lets `-` be a word:

```
10 3 -      \ subtraction   -> 7
10 -3 +     \ negative literal -> 7
```

**Strings** are double-quoted and **may span lines**, as in Perl — a literal
newline inside the quotes is part of the string:

```
catcat> "one
two" print
one
two
```

The escapes are `\n` `\t` `\r` `\"` `\\`, and an unrecognised one is an error
rather than the character itself:

```
catcat> "bad \q escape"
error: unknown string escape '\q'; the escapes are \n \t \r \" \\
catcat> "oops
error: unterminated string: no closing '"' before end of input
```

`"` is self-delimiting like the brackets, so `"a""b"` is two literals. Because a
string runs to its closing quote however many lines that takes, an unclosed one
is reported at end of input rather than at the end of the line — the same trade
the `{ … }` rule makes.

Single quotes and backticks are not lexed. See [U02](U02_Word_Reference.md) §7
for `show`, `cat`, `parse` and `str=`.

**Comments** run from `\` to end of line. `( … )` is a *type annotation*, not a
comment — the one place this language reverses a Forth convention rather than
dropping it. Inside a string a `\` is an escape, not a comment.

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

### Three modes of specification

Everything about a signature is optional, and the effects are optional
*separately* from the stack effect:

| written | stack effect | effects |
|---|---|---|
| `define f { … }` | inferred | inferred |
| `define f ( i64 -- i64 ) { … }` | asserted | inferred |
| `define f ( i64 -- i64 !IO ) { … }` | asserted | asserted |
| `define f ( i64 -- i64 ! ) { … }` | asserted | asserted **empty** |

```
catcat> define b ( i64 -- i64 ) { dup show print dup * }
defined b ( i64 -- i64 !IO )
catcat> define c ( i64 -- i64 ! ) { dup show print dup * }
error: c declares no effects but its body has !IO
```

`b` asserts what it consumes and produces and lets the row follow; the reported
signature is the truth, so `!IO` shows up whether or not you wrote it. This is
what lets you annotate a stack without first knowing every effect the body can
reach — which matters most for recursion, where `!Rec` is an implementation fact
rather than something the author chose:

```
catcat> define fact ( i64 -- i64 ) { dup 0 = if { } then { pop 1 }
                                     else { dup 1 - recurse * } endif }
defined fact ( i64 -- i64 !Rec )
```

**A bare `!` asserts there are no effects.** The sigil is written and its name
is deliberately absent: the effect region is present and empty. Use it where
purity is part of the contract and you want the compiler to hold you to it. It
cannot be combined with a named effect — `( -- ! !IO )` is a contradiction, not
a row — and it is not an effect called `Pure`, because an effect would propagate
to every caller, which is the opposite of what this says.

### Generics

```
define name[#T #U] ( … ) { … }
```

Type parameters are declared in `[…]` and used as `#T` in the signature. A
generic **must** write its signature: inference never generalises, so an
unwritten one would have nothing to generalise from.

```
catcat> define twice[#T] ( #T -- #T #T ) { dup }
generic twice[#T]
catcat> 5 twice
ok  5 5
catcat> "hi" twice
ok  5 5 "hi" "hi"
catcat> define swap2[#A #B] ( #A #B -- #B #A ) { swap }
catcat> 1 "x" swap2
ok  "x" 1
```

**A generic is a template, and each call gets its own copy.** The types come
from the stack at the call: `5 twice` matches `#T` against `i64` and builds a
word that duplicates an `i64`. Nothing polymorphic reaches the compiled program.

Because the copy is made at the call, **the body is checked there too** — so a
generic is fine at every type that satisfies what it does, and fails at the ones
that do not:

```
catcat> define boxy ( Box[i64] -- Box[i64] Box[i64] ) { twice }
error: twice, instantiated: dup: this value's type is not Copy
```

That is linearity (§U02 §4) applying across generics with no extra rule.

Every parameter must be pinned down by the **inputs**, since the outputs are
what the call is trying to work out:

```
catcat> define bad[#T] ( -- #T ) { }
catcat> 1 bad
error: bad: #T is not determined by the inputs, so a call site cannot say what
it should be
```

A `#T` in the signature that names no declared parameter is caught earlier, when
the generic is declared.

A generic body may contain a conditional, carry effects, and abort:

```
catcat> define pick0[#T] ( #T #T bool -- #T ) { if { } then { pop } else { swap pop } endif }
catcat> 1 2 true pick0
ok  1
catcat> "a" "b" true pick0
ok  "a"
catcat> define safe[#T] ( #T -- #T !Fail ) { 1 1 = if { } then { fail } else { } endif }
catcat> try { 9 safe } catch { 0 }
ok  0
```

**What it may not do is call another generic, or call itself.** Each instance is
a separate word created at the call, so an inner one would have to be numbered
after the outer one that contains it, and a self-call would ask for an instance
of itself forever. See §9.

### What inference can and cannot do

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
reserved. See §8.

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

### Declaring one

```
macro name ( slots ) { template }

macro name ( slots )
  alt key ( slots ) { template }
  alt key ( slots ) { template }
end
```

A macro is **a grammar production plus a template**: a fixed run of slots, then
optionally an alternation keyed on a word that is always consumed. It has no
signature and no word id, because it does not exist at run time.

| Slot | Matches | Substituted as |
|---|---|---|
| `{ $x }` | `{ … }` | the block's terms, **spliced** |
| `$x` | one identifier | that word |
| `w` | the literal word `w` | nothing; consumed |

```
catcat> macro sqm ( ) { dup * }
macro sqm
catcat> macro pipe ( { $a } { $b } ) { $a $b }
macro pipe { $a } { $b }
catcat> 3 pipe { 1 + } { 2 * }
ok  8
```

Splicing rather than nesting is why `{ $a $b }` composes two blocks instead of
leaving two blocks on the stack. And an alternation:

```
macro unless ( { $c } then { $t } )
  alt endif ( )              { $c not if { } then { $t } endif }
  alt else  ( { $e } endif ) { $c not if { } then { $t } else { $e } endif }
end
```

`alt` and `end` are keywords only inside this production; both are ordinary
words everywhere else.

### What is guaranteed, and what is not

**The grammar stays LL(1) as it grows.** `ll1_ok` requires that no two macros
share a leading word and no two alternatives of one macro share a key, and
`ll1_extend` *decides* it before accepting a production — so the property holds
at every point in a session, not only for the shipped table.

```
catcat> macro sqm ( ) { 1 }
error: a macro named 'sqm' already exists; two productions on the same leading
word would need a second token to tell apart
catcat> macro bad ( ) alt k ( ) { 1 } alt k ( ) { 2 } end
error: two alternatives of 'bad' share a key, so the token that selects between
them does not
```

**Expansion cannot loop**, and not because anything checks. A template is parsed
against the table *as it stands*, so a macro may use macros declared before it —
already expanded by the time it is registered — and cannot use itself.

**A macro has no stack access.** Its input is syntax and its output is syntax,
so nothing it does is visible at runtime.

**A macro cannot consume the enclosing `}`.** Slots are parsed by the same
functions the block parser uses, so a macro that runs out of tokens inside its
production reports an error rather than reaching past the brace.

**A template cannot read a local it did not capture.** A `$x` naming no slot of
the production is refused when the macro is declared:

```
catcat> macro bad ( { $b } ) { $b $tmp + }
error: 'bad' reads $tmp, which names no slot of the production; a macro body
cannot bind a local, so this would read the caller's $tmp. Add a slot for it, or
correct the spelling
```

That is the whole of hygiene here, and it is a check rather than a renaming pass
because **no term binds a local**: `$x` is a read, and the only binder in the
language is a signature parameter, which appears in a declaration and not in a
term. So a template `$x` naming no slot cannot be a temporary its author
introduced — there is no way to introduce one — and rejecting it at the
declaration names the macro instead of the call site. When `let` arrives this
premise changes and real renaming will be needed.

**A macro takes effect where it is written.** The parser and the evaluator
interleave, one declaration at a time, so `macro sqm ( ) { dup * } 7 sqm` works
on a single line. The price: a parse error part-way through a line no longer
leaves the session untouched, because what came before it has already run. Only
a *lexing* error is free.

**Every shipped macro is an ordinary template**, `if` included — `locate if`
prints its expansion like any other. What a user still could not do is DECLARE
it, because it expands to a `case` and `case` has no surface spelling. That is a
gap in the surface grammar, not in the macro system, and it closes with surface
sums (§9).

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
  if { $c } then { $t } endif
  if { $c } then { $t } else { $e } endif
  \ built in: expands to a case, which has no surface spelling

catcat> locate sqm
macro sqm
  sqm
    -> { dup * }

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
| `bool>sum`, `dispatch …` | a sum elimination that is not the two-branch boolean shape `if` reconstructs |

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

## 6. Effects and handlers

### Declaring an effect

```
effect Counter {
    declare tick  ( -- i64 )
    declare reset ( -- )
}
```

**The signature is not optional here.** An operation has no body, so there is
nothing to infer one from — this is the one place §3's "the signature is
optional" does not apply, and the error says so.

An operation is called exactly like a word, because it *is* one: `tick` is a
`TWord` in the core and typed by the same rule. What it adds is an effect on
the row of everything that calls it.

```
catcat> define twice { tick tick + }
defined twice ( -- i64 !Counter )
```

### `!Eff` in a signature

Effects propagate automatically. Writing them is optional and independent of
writing the stack effect (§3): a signature with no `!` at all infers the row,
and a signature with any `!` asserts it exactly.

```
catcat> define quiet ( -- i64 )          { tick }
defined quiet ( -- i64 !Counter )
catcat> define good  ( -- i64 !Counter ) { tick }
defined good ( -- i64 !Counter )
catcat> define bad   ( -- i64 ! )        { tick }
error: bad declares no effects but its body has !Counter
```

**An operation's effects are not written.** A `declare` inside an `effect` block
belongs to the effect declaring it, so writing anything in its effect region is
refused rather than ignored:

```
catcat> effect E { declare op ( i64 -- i64 !IO ) }
error: declare op: an operation belongs to the effect that declares it, so its
effects are not written
```

`extern` is the same: its row is fixed at `!C !Unsafe`.

### Handling

```
handle Counter over ( i64 ) init { 0 } { tick { dup 1 + } } { tick tick + }
```

A handler is a **stateful object, not a continuation consumer.** An operation
call runs its implementation, which *returns*; nothing is captured, saved or
resumed. `over ( … )` gives the state segment and `init { … }` produces it.

Each implementation is checked at the operation's signature with the state
framed **on top**, so it reads `( args… state -- results… state )`. The state
is the receiver, and a receiver is pushed last:

```
tick  ( state -- i64 state )      \ implemented as  { dup 1 + }
reset ( state -- state )          \ implemented as  { pop 0 }
```

**When the body finishes, the final state is left on the stack**, above what
the body produced — the handler is the object, and the object outlives the
block. So the example above leaves `1 2`: `tick tick +` is `0 + 1`, with the
count `2` on top.

A handler is a term, so it nests inside a definition and discharges the effect
there:

```
catcat> define nostate ( -- i64 ) { handle Counter over ( ) init { } { tick { 5 } } { twice } }
defined nostate ( -- i64 )
```

`over ( )` with an empty `init { }` is the stateless case. It is the degenerate
case of the same rule, not a separate form.

**An operation that is not implemented forwards outward** to the next handler,
which is what makes partial overriding possible. Implementing something that is
not an operation of the named effect is an error.

**Re-entering a handler while its own state is out on loan is reported**, not
served a stale copy:

```
catcat> handle Counter over ( i64 ) init { 0 } { tick { tick swap } } { tick }
STUCK: handler re-entered while its own state is in use
```

That is a dynamic borrow check in a language whose linearity is otherwise
static. It is recorded as an open question, not claimed as the final answer.

### `IO`, and effects only the host can supply

| Word | Signature |
|---|---|
| `print` | `( str -- !IO )` |
| `read` | `( -- str !IO )` |

```
catcat> "42\n" print
42
catcat> define greet ( str -- !IO ) { "hello, " swap cat "!\n" cat print }
defined greet ( str -- !IO )
catcat> "catcat" greet
hello, catcat!
```

`print` writes the string as-is and adds **no newline** — write `"\n"` yourself.
The `i64`-typed `print`/`read` this replaced could not offer the choice.
[U02](U02_Word_Reference.md) §7 covers `show` and `parse`, which are how numbers
get in and out.

These are **ordinary operations of an ordinary effect**. Nothing about the
effect system is special-cased for them, and the only asymmetry is over who may
*declare* one.

**The reserved block** is effects 0–6, and `effect` allocates from 7 upward, so
no program can bring a new host-serviced effect into existence:

| Id | Effect | Discharged by | Operations |
|---|---|---|---|
| 0 | `Dict` | elaboration, or a `handle Dict` frame at runtime. Never printed | every word |
| 1 | `IO` | the REPL, which performs it | `print`, `read` |
| 2 | `Unsafe` | you, with `unsafe { … }` | **none** |
| 3 | `C` | the REPL, which calls libc | each `extern` |
| 4 | `Rec` | you, with `handle Rec` — usually nobody | **none** |
| 5 | `Case` | the handler an `if` elaborates to | one per branch |
| 6 | `Fail` | you, with `try { … } catch { … }` | `fail` |

That is what "suppliable only by the compiler or interpreter" means — a fact
about who owns the identifier, not a restriction the effect system had to grow.

What it does **not** mean is that `IO` is unhandleable. It is an effect like any
other, so you can intercept it:

```
catcat> handle IO over ( ) init { } { print { pop } } { "1" print }
ok  (empty)
```

Nothing was printed: the handler swallowed it. Mocking `IO` for a test is the
same construct as §7's rebinding, reached from the other direction, and it falls
out of the design rather than being added to it.

An `IO` operation with no handler in scope escapes every frame and reaches the
REPL, which is the outermost handler and performs it for real.

A user effect that reaches the top level with nobody handling it is reported
rather than performed:

```
catcat> 1 tick
unhandled: tick escaped with no handler in scope
```

### `Unsafe`: an effect with no operations

`Unsafe` declares nothing. A word carries `!Unsafe` in its row without there
being anything to perform, so unsafety propagates by the ordinary row rules and
**cannot be hidden by forgetting to annotate**. Discharging it is an ordinary
handler, and `unsafe { … }` is a macro for exactly that:

```
catcat> locate unsafe
macro unsafe
  unsafe { $b }
    -> { handle Unsafe over (  ) init { } { } { $b } }
```

There is no keyword and no elaborator case. A word whose row still says
`!Unsafe` *is* an unsafe word, by the same rule that makes `!IO` mean what it
means.

### `Rec`: recursion and loops

A word's own name is **not** in scope inside its body. `recurse` is, and it means
"call the word being defined" — Forth's `RECURSE`, for Forth's reason:

```
catcat> define fact ( i64 -- i64 !Rec ) { dup 0 <= if { } then { pop 1 } else { dup 1 - recurse * } endif }
defined fact ( i64 -- i64 !Rec )
catcat> 5 fact
ok  120
```

**The signature is mandatory.** Inferring the type of a word whose body calls it
is solving a fixpoint, and writing the signature is the missing information:

```
catcat> define f { recurse }
error: f uses 'recurse', which needs a written signature — the signature of a recursive word cannot be inferred from its own body
```

**`!Rec` is what "may not terminate" looks like in a type**, and it propagates
like any other effect:

```
catcat> define fact6 ( -- i64 ) { 6 fact }
error: fact6 declares no effects but its body has !Rec
catcat> define fact6 ( -- i64 !Rec ) { 6 fact }
defined fact6 ( -- i64 !Rec )
```

Carrying it all the way to the top level is the normal outcome, not a problem to
be silenced. `handle Rec over ( ) init { } { } { … }` discharges it if you want
to assert that a particular call does terminate — an unproved claim, exactly as
much of a promise as `unsafe` is.

**A loop is a tail call.** There is no `while`; `recurse` in tail position is one,
and the continuation does not grow:

```
catcat> define countdown ( i64 -- !IO !Rec ) { dup 0 <= if { } then { pop } else { dup show print " " print 1 - recurse } endif }
catcat> 5 countdown
5 4 3 2 1
catcat> define sum ( $n:i64 $acc:i64 -- i64 !Rec ) { $n 0 <= if { } then { $acc } else { $n 1 - $acc $n + recurse } endif }
defined sum ( i64 i64 -- i64 !Rec )
catcat> 100 0 sum
ok  5050
```

A runaway recursion hits the interpreter's fuel bound rather than the machine's
stack:

```
catcat> define spin ( i64 -- i64 !Rec ) { recurse }
catcat> 1 spin
out of fuel
```

**Mutual recursion cannot happen without being marked.** The Dictionary is
ordered: a word may call only words defined before it, and `recurse` is the one
way to name a word that is not yet finished. For two words to call each other,
one of them would have to name a word defined after it, which breaks the
ordering and takes the same `!Rec` mark a self-call does. There is nothing to
detect, because forward references have no spelling.

Anonymous loops are still absent: a macro expands to terms and cannot create the
declaration a self-reference needs to name.

### `Fail`: aborting, and `try` / `catch`

```
try { … } catch { … }
```

`fail` is `( -- !Fail )`. Performing it abandons the rest of the enclosing `try`
block and runs the `catch` block instead. Everything the try block had built is
discarded first, so `catch` starts from the stack that was there before the
`try`:

```
catcat> try { "a" print fail "b" print } catch { }
a
catcat> try { fail "boom" } catch { "recovered" }
ok  "recovered"
```

The two blocks must leave the **same stack**, for the reason two branches of an
`if` must: one of them runs and the code afterwards cannot know which. `catch`
takes **no inputs** — there is nothing left for it to consume.

**Code after a `fail` is checked as live and never runs.** `fail` is `( -- )`,
so the words after it compose exactly as if it had returned, and they have to
typecheck; what they *do* is nothing, because the `try` that catches the `fail`
discards them along with the rest of the block. That is why the `"b" print`
above is checked and silent. `!Fail` reaching the enclosing word is the same
rule doing its ordinary job: a word that calls a `!Fail` word is a `!Fail` word.

```
catcat> define risky ( -- i64 !Fail ) { fail 1 }
defined risky ( -- i64 !Fail )
catcat> define chain ( -- i64 !Fail ) { risky 2 * }
defined chain ( -- i64 !Fail )
catcat> try { chain } catch { 99 }
ok  99
```

`chain` had to declare `!Fail` although it never writes `fail`, and the `2 *` is
typechecked although it can never run.

The reference interpreter builds those dead steps and then drops them, which
costs a walk; a compiler may delete them instead. See D-72 in
[N01](../NOTES/N01_Decisions.md) for why that is licensed and what the pass
needs to know.

`try` discharges `!Fail`, so a word that catches its own failures is pure:

```
catcat> define safediv ( i64 i64 -- i64 !Fail ) { dup 0 = if { } then { fail } else { } endif / }
defined safediv ( i64 i64 -- i64 !Fail )
catcat> define try_div ( -- i64 ) { try { 10 0 safediv } catch { 0 1 - } }
defined try_div ( -- i64 )
catcat> try_div
ok  -1
```

`!Fail` propagates like any other effect, so a word that can fail says so, and
forgetting to write it is an error rather than an omission:

```
catcat> define bad ( i64 -- i64 ) { dup 0 = if { } then { fail } else { } endif }
error: bad declares no effects but its body has !Fail
```

An uncaught `fail` reaches the REPL like any unhandled operation:

```
catcat> fail
unhandled: fail escaped with no handler in scope
```

**`try` and `catch` are not reserved words.** They are keywords only inside this
production, the same way `then` and `endif` are (§8), so both are still
definable as word names.

**Two limits**, both of which want generics:

* **`fail` is `( -- )`, so it cannot stand where a value is expected.**
  `dup 0 = if { } then { fail } else { } endif` works, because both branches
  leave the stack alone. `if { } then { 1 } else { fail } endif` does not: the
  branches disagree, and the `fail` arm would have to be typed at the empty
  type for it to be accepted.
* **The try block runs on a fresh stack.** It may not consume anything that was
  on the stack before it:

  ```
  catcat> 5 try { dup } catch { 0 }
  error: dup: the stack is empty
  ```

  Put what the block needs inside it. This is an elaborator limit and not a
  core one — the core records how deep the block reached, and the elaborator's
  stack model cannot compute that number.

Later, `catch` will be able to take an error value rather than nothing. That is
the same missing feature as the first limit above.

### `extern`: calling C

```
extern name ( signature )
```

Declares a foreign function. The word name **is** the C symbol. The signature is
mandatory — an `extern` has no body to infer one from — and the effects are not
written, because they are always `!C !Unsafe`:

```
catcat> extern strlen ( str -- i64 )
extern strlen ( str -- i64 !C !Unsafe )
catcat> "hello, world" strlen
ok  12
catcat> extern getenv ( str -- str )
extern getenv ( str -- str !C !Unsafe )
catcat> "HOME" getenv strlen
ok  12 15
```

That is libc, linked into the REPL — `strlen(3)`, not an imitation of it.
Available today: `strlen`, `puts`, `abs`, `time`, `getpid`, `getenv`. The set is
a fixed table in `bin/catcat_c.c` rather than `dlsym`, because calling an
arbitrary symbol needs libffi to build a call frame at runtime; nothing on the
catcat side would change if it did.

Only `i64` and `str` cross the boundary, and at most one value comes back. Both
are checked **where the `extern` is written**, not where it is called:

```
catcat> extern f ( bool -- )
error: extern f: only i64 and str cross the C boundary so far
```

**Unsafety propagates, and the signature check catches it:**

```
catcat> define namelen ( str -- i64 ) { strlen }
error: namelen declares no effects but its body has !C !Unsafe
catcat> define namelen ( str -- i64 !C ) { unsafe { strlen } }
defined namelen ( str -- i64 !C )
```

The second vouches for the memory safety of the call and still admits, in its
type, that it talks to C.

**And `C` is handleable, so a foreign call can be mocked** — no test double, no
linker flag, no build variant:

```
catcat> define mocked ( str -- i64 ) { handle C over ( ) init { } { strlen { pop 99 } } { namelen } }
defined mocked ( str -- i64 )
catcat> "abcd" mocked
ok  99
```

A declared `extern` the host does not implement is reported at the *call*, as an
operation that escaped — which is what it is:

```
catcat> extern nosuchfn ( -- i64 )
extern nosuchfn ( -- i64 !C !Unsafe )
catcat> nosuchfn
unhandled: nosuchfn escaped with no handler in scope
```

---

## 7. Rebinding words with `with`

```
with { old new … } { body }
```

Runs `body` with words rebound. It is sugar for a `Dict` handler (§6):
`with { a b } { … }` elaborates to `handle Dict over ( ) init { } { a { b } } { … }`
and is then **discharged during elaboration**, so it leaves *nothing* in the
compiled program.

```
catcat> define noisy ( i64 -- i64 !IO ) { dup show print }
catcat> define quiet ( i64 -- i64 )     { 1 * }
catcat> define t2 { with { noisy quiet } { noisy noisy } }
defined t2 ( i64 -- i64 )
catcat> locate t2
define t2 ( i64 -- i64 ) {
  quiet quiet
}
```

Two things are worth reading off that transcript. The `with` is *gone* from the
decompiled body — it cost nothing, because it was resolved before the program
existed. And `t2` is **pure**: rebinding an `!IO` word to a pure one removes the
effect from the row. Reinterpreting a program by overriding the words it calls
is the intended use.

**The replacement must have the same signature.** Effects may differ freely —
that is the point — but the stack effect may not, because the body is
elaborated against the original.

```
catcat> define bad2 { with { slow not } { 1 } }
error: with: not cannot replace slow; their signatures differ
```

**`with` reaches through a definition**, because it *is* a `Dict` handler —
elaborated to one, then discharged at elaboration time:

```
catcat> define greet ( -- str ) { "hello" }
catcat> define bye   ( -- str ) { "goodbye" }
catcat> define shout ( -- str ) { greet "!" cat }
catcat> define w ( -- str ) { with { greet bye } { shout } }
catcat> w
ok  "goodbye!"
catcat> locate w
define w ( -- str ) {
  bye "!" cat
}
```

The `greet` being rebound is inside `shout`, not in the block, and the rebinding
still finds it. The residual shows why: `shout` was inlined and the call
rewritten, so nothing about the `with` survives.

The same thing spelled dynamically gives the same answer (§6):

```
catcat> handle Dict over ( ) init { } { greet { bye } } { shout }
ok  "goodbye!"
```

That is the point. `with` is resolved at elaboration and costs nothing;
`handle Dict` is a frame consulted at the call and costs a lookup; **the result
is the same**, because they are one construct resolved at two times. Both are
type-checked by the ordinary handler rule, which types the replacement at the
declared signature of the word it replaces.

**How much gets inlined depends on definition order**, and only the residual's
size depends on it, never the answer. The discharge pass walks the words once
from newest to oldest, so a replacement defined *after* the word it replaces
survives as a call while one defined *before* is inlined in turn.

A `Dict` handler may carry state, so it is a class over a word:

```
catcat> define twice ( -- str ) { greet greet cat }
catcat> handle Dict over ( i64 ) init { 0 } { greet { 1 + dup show swap } } { twice }
ok  "12" 2
```

---

## 8. No lookahead

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

## 9. Not yet implemented

Each is specified in [D05](../P00_Design/D05_Surface_Syntax_and_Macros.md) and
absent from the implementation. Listed because the gap between the two documents
is otherwise invisible.

| Feature | State |
|---|---|
| mutual recursion | impossible without being marked, since the Dictionary is ordered and there are no forward references (§6) |
| anonymous loops | none; a loop is `recurse` inside a `define` (§6) |
| a generic body calling another generic | refused (§3): an instance is an ordinary word, so an inner one would be numbered after the outer one containing it. Installing instances innermost-first and renumbering the call would lift it |
| recursion in a generic | refused, deliberately: an instance is minted per call site, so a self-call would request itself forever |
| `let` and `let (…)` | not parsed |
| generators, coroutines | not parsed; they wait on staging, not on handlers |
| sums, classes, `module`, `::`, `.` | not parsed |
| quotation `'…'`, backtick | not lexed. Strings ARE lexed (§2) |
| a `case` a user can write | `if` is an ordinary macro, but its expansion has no surface spelling, so a user cannot declare the same production (§5). Closes with surface sums |
| macro hygiene beyond the declaration check | §5's check is complete while no term binds a local. `let` will change that premise and need real renaming |
| macros as words | a macro is a template, not a program; the eventual design is an ordinary word with an effect that consumes code, which needs the elaboration-time interpreter |
| `Box`/`Rc` construction | types exist; no surface word builds one |
| source positions in errors | absent — errors are messages without spans |
| arbitrary C symbols | `extern` reaches a fixed table of six libc functions ([U02](U02_Word_Reference.md) §7a); `dlsym` plus libffi would lift it, and nothing on the catcat side would change |
| C types beyond `i64` and `str` | refused at the `extern`, not at the call |
| `fail` at a value type | `fail` is `( -- )`, so it cannot stand where a value is expected (§6); it wants the empty type, which wants generics |
| a typed `catch` | `catch` takes no inputs; an error payload wants generics (§6) |
| a `try` block reading the enclosing stack | the block runs on a fresh stack (§6). The core does not restrict this — the elaborator's stack model cannot compute how deep a block reached |
| `fail` at a value type | `fail` is `( -- )`, so it cannot stand where a value is expected (§6); it wants the empty type, which wants generics |
| a typed `catch` | `catch` takes no inputs; an error payload wants generics (§6) |
| a `try` block that reads the enclosing stack | the block runs on a fresh stack (§6); the core does not restrict this, the elaborator does |

Seven entries left this table recently and are worth naming, because a reader of
an older copy will look for them. `!Eff` in a signature used to be **parsed and
silently dropped** — the misleading gap — and is now resolved and checked (§6).
Effects and handlers used to be absent entirely. User-defined macros used to be
listed here as needing the elaboration-time interpreter; the template form (§5)
turned out to need nothing. **Mutual recursion** used to be undetected and is
now impossible without being marked (§6). **Macro hygiene** used to be listed
flatly as absent; it turned out to be a check rather than a renaming pass, for
the reason §5 gives, and the entry above records only what is left of it. And
**dynamic `with`** used to say there was no runtime dictionary lookup; there is,
spelled `handle Dict` (§7). And **`#T` generics** used to parse and be rejected;
they run (§3), with the two entries above recording what is left of them.

**Handler state aliasing is checked at runtime**, not statically (§6). That is a
gap in a different sense: the language is safe, but the check is dynamic where
everything else about linearity is static.

**A handler that implements none of its effect's operations still discharges the
effect from the row.** The typing rule removes the effect unconditionally, while
the machine forwards an unimplemented operation to the next handler out — so

```
catcat> handle IO over ( ) init { } { } { "x" print }
x
```

reports a pure signature and still prints. Nothing about `try` introduced this;
it is why `unsafe { … }` and `handle Rec` work, since those effects have no
operations to leave unimplemented. It is tracked as Q-16 in
[N02](../NOTES/N02_Open_Questions.md).

**A macro shadows a word silently.** Declaring `macro foo …` makes every later
`foo` a macro invocation, whatever `foo` was bound to. `locate` reports the macro
first, for exactly that reason, but nothing warns at the point of declaration.
