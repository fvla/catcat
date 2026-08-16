# U03 — Tutorial

A path into the language. [U01](U01_Grammar.md) is the grammar reference and
[U02](U02_Word_Reference.md) is the word reference; both are for looking things
up, and neither tells you where to start.

> **Current as of commit `68aec2c`.**
> Source of truth: the binary. Every transcript below was produced by running
> it, and most are quoted from [`demos/`](../demos/README.md), which `make
> demos` checks against golden output. If a transcript here and the binary
> disagree, the binary is right — say so in an issue, because it means this
> file went stale.

---

## 0. Running it

```
make catcat
./_build/default/bin/catcat.exe
```

That is a REPL. It also runs non-interactively, which is how the demos and the
tests work:

```
./_build/default/bin/catcat.exe '2 3 +' '6 dup *'
./_build/default/bin/catcat.exe -f demos/01_tour.cat
```

The stack persists between lines and is printed after each one, bottom-to-top.
`:q` quits, `:s` shows the stack.

**Every transcript below starts from an empty stack.** Since results accumulate,
typing them one after another in one session gives you the same values with the
earlier ones still underneath.

---

## 1. Everything is a stack

catcat is concatenative: a program is a sequence of words, each of which
transforms the stack, and juxtaposition is the only way to combine them. There
are no expressions, no parentheses around arguments, and no precedence.

```
catcat> 2 3 +
ok  5
```

**The top of the stack is the right operand.** So `10 3 -` is 7, not −7:

```
catcat> 10 3 - show print "\n" print
7
```

`show` renders a number as a string and `print` writes it. There is no
automatic newline — `"\n" print` is how you get one, which is why these lines
are longer than you might expect.

---

## 2. Defining a word, and reading a signature

```
catcat> define sq { dup * }
defined sq ( i64 -- i64 )
```

You did not write `( i64 -- i64 )`. **Signatures are inferred**, and the REPL
prints the one it worked out. This is not a convenience feature; it falls out
of the language, because composing programs *is* composing signatures.

A signature reads left to right, bottom of the stack to top, with **the top on
the right**:

```
( i64 i64 -- i64 )      \ takes two numbers, leaves one
( str -- )              \ takes a string, leaves nothing
( -- str )              \ takes nothing, leaves a string
```

Writing one is an **assertion**, checked against what the body does:

```
catcat> define cube ( i64 -- i64 ) { dup dup * * }
defined cube ( i64 -- i64 )
catcat> define wrong ( i64 -- str ) { dup * }
error: wrong declares ( i64 -- str ) but its body has ( i64 -- i64 )
```

### Locals

`dup`, `pop` and `swap` reach the top two slots, and no composition of them
reaches a third. So when you need a third, name it:

```
catcat> define hypotsq ( $x:i64 $y:i64 -- i64 ) { $x $x * $y $y * + }
defined hypotsq ( i64 i64 -- i64 )
catcat> 3 4 hypotsq
ok  25
```

`$x` is not a variable — it compiles to stack shuffles and the core never
learns that locals existed. `locate` will show you:

```
catcat> locate hypotsq
define hypotsq ( i64 i64 -- i64 ) {
  pick.1 pick.2 * pick.1 pick.2 * + roll.1 pop roll.1 pop
}
```

`locate` decompiles the stored core term. **There is no source text kept
anywhere** — what you see is what the elaborator produced, which makes it the
tool for finding out what a construct actually cost.

---

## 3. Branching and looping

```
if { cond } then { conseq } else { alt } endif
```

The **condition block runs inline** and leaves a `bool`. It is often empty,
because the bool is already there:

```
catcat> define abs { dup 0 < if { } then { 0 swap - } endif }
defined abs ( i64 -- i64 )
catcat> -5 abs
ok  5
```

`endif` is mandatory and `else` is not. An omitted `else` is `else { }`, so
"the `then` branch must not change the stack" is not a separate rule — it is
what branch agreement says when the other branch is empty.

There is no `while`. A loop is a tail call, and a word's own name is not in
scope in its body — `recurse` is:

```
catcat> define fact ( i64 -- i64 !Rec ) { dup 0 <= if { } then { pop 1 } else { dup 1 - recurse * } endif }
defined fact ( i64 -- i64 !Rec )
catcat> 10 fact
ok  3628800
```

**The signature is mandatory on a recursive word**, because inferring the type
of a word that calls itself is solving a fixpoint.

That `!Rec` is your first effect. It means "may not terminate", and it is in
the type because that is a fact about the word worth carrying. It propagates:

```
catcat> define fact10 ( -- i64 ) { 10 fact }
defined fact10 ( -- i64 !Rec )
```

You wrote the stack effect and got the row for free — writing one does not mean
writing the other. A bare `!` is how you assert there are *no* effects, and it
is held to:

```
catcat> define pure10 ( -- i64 ! ) { 10 fact }
error: pure10 declares no effects but its body has !Rec
```

**Full example: [`demos/01_tour.cat`](../demos/01_tour.cat).**

---

## 4. Effects: saying what, not how

This is the part the language is for.

An effect is a set of operation signatures. Declaring one gives you words you
can call without deciding what they do:

```
catcat> effect Log { declare say ( str -- ) }
effect Log say
catcat> define step1 ( i64 -- i64 !Log ) { "  squaring\n" say dup * }
catcat> define step2 ( i64 -- i64 !Log ) { "  adding one\n" say 1 + }
catcat> define pipeline ( i64 -- i64 ) { step1 step2 }
defined pipeline ( i64 -- i64 !Log )
```

`pipeline` never mentions `say`, and picks up `!Log` anyway. Called with no
handler, the operation escapes:

```
catcat> 3 pipeline
unhandled: say escaped with no handler in scope
```

A **handler** supplies the meaning. Here are four, over the same four words,
unmodified:

```
catcat> handle Log over ( ) init { } { say { print } } { 3 pipeline }
  squaring
  adding one
ok  10

catcat> handle Log over ( ) init { } { say { pop } } { 3 pipeline }
ok  10
```

The second is *pure* — not "pure except for logging", pure, and a caller may
treat it as such.

A handler may carry **state**, which is what makes it an object rather than a
function. `over ( … )` declares the state segment and `init` gives its value;
the state sits on **top** of each operation's arguments, and the handler leaves
its final state above the result:

```
catcat> handle Log over ( i64 ) init { 0 } { say { swap pop 1 + } } { 3 pipeline }
ok  10 2
```

Two messages, result 10. Or make the log a *value* instead of a counter:

```
catcat> handle Log over ( str ) init { "" } { say { swap cat } } { 3 pipeline }
ok  10 "  squaring
  adding one
"
```

No file, no buffer, no IO — the same program.

### The rules worth knowing early

- **Handlers nest**, and an operation reaches the nearest one out.
- **An implementation may itself perform operations**, so a handler is a
  transformer and not only a sink.
- **A handler may not re-enter itself.** Its state is lent to the
  implementation while that runs, so an operation reaching the same frame gets
  `STUCK: handler re-entered while its own state is in use`. Wrap a *different*
  word instead — see §5.

**Full example: [`demos/02_effects_bottom_up.cat`](../demos/02_effects_bottom_up.cat).**

---

## 5. The Dictionary: rebinding words from outside

§4 needed the program to declare `!Log`. This section needs nothing from the
program at all.

The map from a name to what it means is itself an effect, `Dict`, present in
every program and never written down. So the words a program calls can be
rebound from outside it:

```
catcat> define rate  ( -- i64 )          { 10 }
catcat> define tax   ( $amt:i64 -- i64 ) { $amt rate * 100 / }
catcat> define total ( $amt:i64 -- i64 ) { $amt $amt tax + }
catcat> 200 total
ok  220

catcat> define eu_rate ( -- i64 ) { 20 }
catcat> define eu_total ( $amt:i64 -- i64 ) { with { rate eu_rate } { $amt total } }
catcat> 200 eu_total
ok  240
```

`rate` is called inside `tax`, which is called inside `total`. The `with` block
does not lexically contain that call and `rate` is nobody's parameter — the
rebinding reaches it anyway.

**And it costs nothing.** `with` is discharged while the program is being
built, so it is not in the compiled program:

```
catcat> locate eu_total
define eu_total ( i64 -- i64 ) {
  roll.0 pick.0 pick.1 roll.0 eu_rate * 100 / + roll.1 pop
}
```

The same rebinding spelled dynamically gives the same answer, resolved at the
call instead:

```
catcat> handle Dict over ( ) init { } { rate { eu_rate } } { 200 total }
ok  240
```

That is the design's central bet, visible in two lines: **specialization and
JIT are the same operation**, differing only in when they run.

### A profiler, over code that knows nothing about profiling

A `Dict` handler may carry state, so it is a class over a *word*:

```
catcat> define tax_impl ( $amt:i64 -- i64 ) { $amt rate * 100 / }
catcat> handle Dict over ( i64 ) init { 0 } { tax { swap tax_impl swap 1 + } } { 200 total }
ok  220 1
```

`tax` is an ordinary word, not an operation. It has no effect in its signature,
`total` was compiled against the real one, and the handler intercepted it
anyway. (The wrapper is a separate word because calling `tax` inside its own
replacement would re-enter the frame — §4's last rule.)

**Full example: [`demos/03_dictionary_top_down.cat`](../demos/03_dictionary_top_down.cat).**

---

## 6. Generics

Type parameters go in `[…]` and appear as `#T`. A generic **must** write its
signature — inference never generalises, so there would be nothing to
generalise from.

```
catcat> define twice[#T] ( #T -- #T #T ) { dup }
generic twice[#T]
catcat> 5 twice
ok  5 5
catcat> "hi" twice
ok  5 5 "hi" "hi"
```

Each call gets its own copy, spliced into the caller. Nothing polymorphic
reaches the compiled program:

```
catcat> define quad[#T] ( #T -- #T #T #T #T ) { twice twice twice }
catcat> define q ( i64 -- i64 i64 i64 i64 ) { quad }
catcat> locate q
define q ( i64 -- i64 i64 i64 i64 ) {
  dup dup dup
}
```

Write the types out when the stack cannot supply them — which is any parameter
that appears only in the output:

```
catcat> define mk0[#T] ( -- #T ) { 0 }
catcat> mk0
error: mk0: #T is not determined by the inputs; write the types at the call site, as in mk0[i64]
catcat> mk0[i64]
ok  0
```

Written types are checked, not believed:

```
catcat> mk0[str]
error: mk0, instantiated: declares ( -- str ) but its body has ( -- i64 )
```

Because the copy is made at the call, **the body is typechecked there** — so
linearity crosses generics with no extra rule:

```
catcat> define boxy ( Box[i64] -- Box[i64] Box[i64] ) { twice }
error: twice, instantiated: dup: this value's type is not Copy
```

Two limits to know: a generic **may not call itself**, directly or through
another, because a call is expanded where it stands; and **`with` does not
reach into an instance**, because the instance resolved its own calls when it
was built.

**Full example: [`demos/04_generics_and_staging.cat`](../demos/04_generics_and_staging.cat).**

---

## 7. Failing

`fail` is the one operation of the `Fail` effect and `try`/`catch` is its
handler. Nothing about it is special-cased.

```
catcat> define validate ( $n:i64 -- i64 !Fail ) { $n 0 < if { } then { fail 0 } else { $n } endif }
catcat> try { 7 validate } catch { 0 }
ok  7
catcat> try { -7 validate } catch { 0 }
ok  7 0
```

Two things in that snippet are gaps rather than design, and it is worth knowing
which:

- **`fail 0`.** `fail` is `( -- !Fail )`, so it cannot stand where a value is
  expected, and the `0` is unreachable padding to make the branches agree. What
  is wanted is `fail` at the empty type.
- **The value is produced inside the block.** A `try` block runs on a *fresh*
  stack: it cannot see what was already there, and it cannot see a local
  either, since a local is a stack slot. This is the main thing standing
  between `try` and ordinary use.

```
catcat> define or_zero ( $n:i64 -- i64 ) { try { $n validate } catch { 0 } }
error: unbound local $n
```

`catch` receives nothing and must leave what the try block would have left.

**Full example: [`demos/06_failure.cat`](../demos/06_failure.cat).**

---

## 8. Calling C

```
catcat> extern strlen ( str -- i64 )
extern strlen ( str -- i64 !C !Unsafe )
catcat> unsafe { "hello, world" strlen }
ok  12
```

The word name **is** the C symbol; the signature is mandatory; the row is not
written, because it is always those two effects. `!C` says this talks to C and
`!Unsafe` says nobody has checked that the call is memory-safe. `unsafe { … }`
is how you vouch for the second — it is a handler for an effect with no
operations, so it is a claim, not a check. Note `!C` survives it.

And because `C` is an effect like any other, **you can handle it**:

```
catcat> define session_tag ( -- i64 !C ) { unsafe { "HOME" getenv strlen getpid + time + } }
catcat> define fixed ( -- i64 ) {
          handle C over ( ) init { } {
            getenv { pop "/home/tester" }  strlen { pop 12 }
            getpid { 4242 }               time   { 1700000000 }
          } { session_tag }
        }
catcat> fixed
ok  1700004254
```

Same answer on every machine and in every second. That is a unit test of code
that calls libc, with no test double, no link-time seam and no build variant —
and `fixed` is **not** `!C`, because handling the effect discharged it.

**Full example: [`demos/05_mocking_c.cat`](../demos/05_mocking_c.cat).**

---

## 9. Putting it together

[`demos/07_three_modes.cat`](../demos/07_three_modes.cat) is the one to read
when you want the point in a single file: one deployment script, no `--dry-run`
flag and no branch anywhere in it, run three ways.

```
effect Deploy {
    declare fetch   ( str -- str )
    declare install ( str -- )
    declare restart ( str -- )
}

define one    ( $svc:str -- !Deploy ) { $svc fetch install $svc restart }
define script ( -- !Deploy )          { "web" one "db" one "cache" one }
```

`script`'s type says exactly what it can touch. It cannot print, cannot call C
and cannot fail. Three handlers later it has run for real, narrated a dry run,
and been folded into a step count — and the third is a **pure function**, so it
is something a test can compare.

Nothing was injected. `script` takes no handler parameter, holds no reference
to one, and was compiled before any of the three existed.

---

## 10. What is not here yet

The honest ceiling: **there are no arrays, no lists, no records and no string
indexing.** Everything above is control- and effect-shaped, and demo 07 ends
with three service names written out as literals for exactly that reason.

[U01 §9](U01_Grammar.md#9-not-yet-implemented) is the full list of what is
specified and absent. [`NOTES/N04_Roadmap.md`](../NOTES/N04_Roadmap.md) §4 is
what is planned and why in that order — the short version being that arrays
turn out to be downstream of a *library mechanism*, not of a memory model.

## Where to go next

| You want | Read |
|---|---|
| the grammar, precisely | [U01](U01_Grammar.md) |
| what a word does | [U02](U02_Word_Reference.md) |
| runnable versions of everything above | [`demos/`](../demos/README.md) |
| why a thing is the way it is | [`NOTES/N01_Decisions.md`](../NOTES/N01_Decisions.md) |
| the mechanized core | [`P01_Specification/M00_Reading_Guide.md`](../P01_Specification/M00_Reading_Guide.md) |
| the language as *designed*, which is larger | [`P00_Design/`](../P00_Design/) |
