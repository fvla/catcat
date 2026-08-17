# N05 — Elaboration-time macros: the plan

Written 2026-08-17, after step C (`b828543`). This file exists because the plan
it replaces was wrong in an instructive way, and the replacement is large enough
that a thread should be able to pick it up cold.

`N04` §4 is the feature sequencing and stays the index. This is the detail for
one entry in it.

---

## 0. Why there is a new plan

D-89 step 3 said: macros reach declaration position, and the record form becomes
a macro. Step C built `seal`, so the type a record needs exists. Running the
test turned up an obstacle that is not about declaration position — **a record's
field count is not fixed and macro slots are** (D-96), so the production would
need repetition, which D-35 excluded on purpose.

The answer is not repetition slots. It is that **`( … )` is a deferred-parse
group** — `INITIAL_DRAFT_1.md:86`, "() corresponds to any block which doesn't
use the default lexer/parser, so lexing/parsing can be deferred" — so a macro
parses the group's contents itself and the variable arity lives inside the
macro's own loop. The production grammar never becomes variadic.

That is D05 §5's stated target reached from a different direction: *"a macro
should be an ordinary word with an effect that lets it consume and transform
code"*. The template form was always a placeholder for it. So this is not a
detour to unblock records; records are the first client of the thing the design
has been pointing at since the draft.

**Settled by the user, 2026-08-17** (recorded as D-97):

1. A macro **may not read past its group**. Its input is the group and nothing
   else.
2. A macro's signature carries **`!Rec`** if it may not terminate. Signatures
   stop being ornamental; this is the language's existing answer to the same
   question and it keeps one rule.
3. **Hygiene must be re-derived rigorously.** D-73's argument does not survive.
4. **Emission is typed quotation, not tokens.** Untyped token emission gives
   weird parse errors and no hygiene. `'` is the operator; `emit` is the word it
   is sugar for. `'word` emits `word`; `'{0 >}` emits `0 >`.

---

## 1. The shape of the thing

A macro becomes a **program that runs during elaboration**. It:

- reads its group through an effect, rather than receiving a list;
- builds syntax by quotation, rather than substituting into a template;
- emits that syntax where the macro call stood;
- and may **run** a `{ }` block it was given, at elaboration time, with the
  block's effects becoming its own.

Four properties are load-bearing and must survive every phase:

| Invariant | Why it must not be lost |
|---|---|
| the default parser stays LL(1) | D-30; the verified CFG-to-recursive-descent generator has to be able to describe it |
| a group is self-delimiting, so its extent is known **without running anything** | an LSP must be able to reparse a region; this is the whole reason macros may not read past their group |
| what is emitted is *parsed syntax*, never text | no macro-induced parse errors, and hygiene has something to attach to |
| an expansion-time effect is **declared** | a macro that does IO at compile time says so in its row |

---

## 2. The crux: what unit does `emit` take?

This is the one question the rest depends on, and it is the one to settle first.

A `record` has to emit `seal Point ( i64 i64 ) { … }` where the number of types
between the parens comes from the group. So the macro must accumulate a
**variable-length fragment**. Three ways:

**(a) Whole phrases only.** `emit` takes a complete declaration. Then the field
types must be accumulated as a *list value* before the declaration is built —
and lists need recursive types, which is N02 Q-13. **Blocked.**

**(b) Kinded fragments with concatenation** — *the lean*. `Code[k]` is an
opaque syntax value with a kind: `Code[Types]`, `Code[Terms]`, `Code[Decls]`.
Quotation produces one, concatenation combines two of the same kind, and
builders turn fragments into larger fragments:

```
'( i64 )                     \ Code[Types]
$acc $one code-cat           \ Code[Types] Code[Types] -- Code[Types]
$name $acc seal-decl         \ str Code[Types] -- Code[Decls]
emit                         \ Code[Decls] -- !Parse
```

Accumulating N fields is a **fold with a binary operator**, not a list — so it
needs no list type and does not wait on Q-13. The kind index uses the type
parameters that shipped in step B. Hygiene has a place to live: each `Code`
value can carry the environment it was written against.

The cost is a builder per syntactic form — an API mirroring `E02.sdecl`. That is
real work, and it is also exactly what makes emission typed rather than textual.

**(c) Token fragments.** Cheapest, rejected by the user, and correctly: it is
text with extra steps.

**Decision needed before phase 2 starts.** Everything below assumes (b).

### How `Code` is typed

`Code[k]` values exist only at elaboration time (D01 §3.2: code is first-class
at elaboration time, functions are not), but M06 still has to type the macro
body that pushes them. Three options:

- **`M01.prim` gains `PCode`.** Blocked by module order: `M02.prim_rep` would
  have to name `M05.term`, and M02 is before M05.
- **A prelude `seal Code[#K] ( )` with no `pack` and no `unpack`** — *the lean*.
  Statically a well-formed nominal type with no capabilities, so code is
  **linear**, which is arguably right: a fragment is emitted once. No program can
  build or open one, so the empty representation is never observed. Reachable
  with exactly what step C shipped.
- **A new `M01.dtype` constructor.** Heaviest; touches every module.

The residual risk in the lean is that the static representation (`[]`) and the
runtime value disagree, since `R01.rvalue` would gain an `RCode` case carrying a
`term`. `R04.erase` and `M06` have to be checked for that. This is the same
problem an `extern` type will have — a C `FILE*` is an opaque host value — so
solving it here is not a special case.

---

## 3. Syntax

**`'` becomes self-delimiting.** `E01.is_delim` is `{ } ( ) [ ] : "` today;
adding `'` makes `'word` lex as two tokens with no lookahead, and `'{` as two.
D05 §6 already reserves `'`, so this is sanctioned rather than novel — but it is
a **lexical break**: any word name containing an apostrophe stops being one
word. That is the `--` lesson (D-28) and belongs in the commit message.

After `TkQuote` the token in hand decides: a word, or `{`. LL(1), no lookahead.

**A quoted block is parsed as a declaration sequence**, not a term sequence.
`parse_decl` already falls through to `SdExpr terms`, so `'{ 0 > }` and
`'{ seal Point ( i64 i64 ) { … } }` are read by the same function and the first
lands in the expression case. This is what lets a macro emit declarations
without a second quotation form.

**Splicing a capture into a quotation** is the piece with the hygiene question
attached, and it is deliberately not settled here. The continuity argument says
`$x` — that is what a template means today. The objection is that `$x` inside a
quotation then cannot mean "the emitted code reads a local `x`", and the escape
hatch is exactly the thing hygiene has to define. See §6.

---

## 4. Reading the group

`( … )` in term position is currently a parse error — "unexpected ( in a term
sequence" — so the syntax is free.

The group is handed to the macro **through an effect**, not as a value:

```
effect Parse {
    declare more ( -- bool )
    declare next ( -- Token )
    declare emit ( Code[Decls] -- )
}
```

This is what makes the whole thing fit without waiting on Q-13: each operation
has a fixed signature, so the macro stays statically stack-typed while consuming
an unbounded group, and nothing needs a list type. The loop is `recurse`, which
is why `!Rec` in the row is the honest termination story rather than a hidden
fuel counter.

`Token` is a flat sum and is declarable with what step B shipped:

```
data Token { alt TkWord ( str ) alt TkInt ( i64 ) alt TkStr ( str )
             alt TkArrow ( ) alt TkLBrace ( ) … }
```

`eff_parse` takes reserved id **7** and `eff_user_base` moves 7 → 8
(`R03_Prelude.fst:76`). Its stage is `SStatic` — `M04.stage` already exists and
`M04.all_static` is already the predicate — so a `!Parse` that survived to
runtime is a type error and not a special case.

---

## 5. Phases

Each is independently committable, and `make verify` plus `make demos` gate each
one. The goldens are the regression test that matters: phases 1 and 2 must leave
every existing demo transcript **byte-identical**.

| | Phase | Deliverable | Depends on |
|---|---|---|---|
| 1 | **Expansion moves out of the parser.** `E03` is a pure function with no session; a macro that computes has to run. Expansion moves to `E06` and the parse becomes suspendable — the same shape as `suspension`/`LEffect`, which already suspends evaluation mid-line for the host. | no user-visible change; goldens prove it | — |
| 2 | **`Code`, `'`, `emit`.** Quotation, the kinded fragment type, concatenation, and `emit`. The template form is re-expressed as a program that emits its template, and `if` / `try` / `unsafe` are rewritten that way. | macros are programs; goldens unchanged | 1, §2 decision, §6 hygiene |
| 3 | **Groups and `Parse`.** `( … )` as a deferred group, the `Token` type, `more` / `next`, and the group slot in a production. | a macro that reads arbitrary-length syntax | 2 |
| 4 | **Declaration builders.** `seal-decl`, `define-decl`, … enough to write `record`. Macros reach declaration position, which falls out: what is emitted is a `Code[Decls]`, and where the macro stood is a declaration position. | **`record`**, closing D-96 and Q-24 | 3 |
| 5 | **`run`.** A `{ }` block a macro holds is executed at elaboration time; its effects join the macro's row; the elaborator suspends to the host exactly as `eval_line` already does. | functors — the draft's SIMD case; D-02's second running witness | 2 |
| 6 | **`macro` collapses into `define`.** A macro is an ordinary word whose row contains `!Parse`, per D05 §5's target. The `macro` declaration becomes sugar or is deleted. | one construct instead of two | 4, 5 |

Phases 1–4 are what records need. Phase 5 is the larger idea and is worth
keeping separate; phase 6 is the tidy-up that makes the claim true.

---

## 6. Hygiene, which has to be re-derived

D-73's argument is that hygiene reduces to a well-formedness check, because
**no `sterm` binds a local**: `$x` is a read, the only binder is a signature
parameter, and a signature appears in a declaration while a macro body is a term
list. A macro that emits declarations breaks every clause of that. It can emit a
signature, so it can bind; and `$x` inside a quotation has two possible
meanings.

What has to be answered, precisely:

1. **Where does a name in emitted code resolve** — the macro's environment, or
   the call site's? Both are wanted: a macro's own helper words should resolve
   where the macro was written; a name the macro was *given* must resolve where
   it was given.
2. **What does `$x` inside a quotation mean**, and what is the escape for the
   other meaning?
3. **What happens when a macro emits a binder** whose name collides with one at
   the call site?

The line of attack worth trying first, because the language already has the
mechanism: **name resolution is already first-class here.** The Dictionary is
ordered, `with` rebinds it, and `!Dict` is the effect that says a word's meaning
depends on it (D-37, D-63). A `Code` value carrying the dictionary it was
written against, and splicing being a `with`-like rebinding, would make hygiene
a *use* of the effect system rather than a pass bolted beside it. D-86 already
made the ambient dictionary follow into nested scopes, which is the same
question one level down.

This is a design obligation, not a task, and it gates phase 2. It should end up
in `N01` as its own decision with the argument written out — not as a paragraph
in a commit message.

---

## 7. What this does not reach

**Code cannot be *inspected*.** Quote it, concatenate it, emit it, run it,
forward it — yes. Walk a term tree and rewrite it — no: that needs a tree value,
which needs recursive types, which is Q-13. So phase 5 buys functors and
compile-time evaluation, not a term rewriter. Worth stating up front so it is
not discovered halfway.

**Compile-time IO is possible and must stay visible.** A macro that runs a block
performing `!IO` makes the *compiler* do IO. That is intended — it is what a
build-time code generator is — and the guard is that the row says so.

---

## 8. Independent work, deliberately not in this plan

Three items are cheap, unrelated, and do not interact with any of the above.
They are the right thing to interleave if this stalls:

- **`bool` as a declared two-variant sum**, deleting `M05.PBoolSum` and
  `M01.prim.PBool`. Step B was supposed to unlock this and nothing has claimed
  it.
- **`option`**, so `parse` and `getenv` stop returning `0` and `""` as
  sentinels.
- **`fail` at the empty type** (D-71). The core already has it: `TSum []` is
  uninhabited and `M06.infer` rejects `TDispatch [] []` only on `Nil? variants`.

---

## 9. Where the old plan's records went

`seal Point ( i64 i64 ) { cap copy cap drop pack Point unpack p_open }` is a
record today, with capabilities and an identity, and its accessor is three lines
by hand (D-96, `DOCS/U03` §9a). What phase 4 adds is the field names and the
generated accessors — sugar over a type that already exists. Nothing in the type
system is waiting on this.
