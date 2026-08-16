# M00 — a reading guide to the mechanized core

**Current as of commit `68aec2c`.**

This is a map, not an authority. Everything here is derived from `M01`–`M11`
and **the modules win on any disagreement** — they are checked by F\*, and this
file is checked by nobody. Where it says a theorem is proved, `make verify`
plus `make admits` is how you confirm it.

Written because the specification is 4,200 lines of F\* and nothing tells you
which 400 of them carry the design. These do.

---

## 0. If you have twenty minutes

Read, in this order, and nothing else:

1. **`M05_Terms.fst`, the `term` declaration** (~line 153). Eight constructors.
   That is the entire language; everything a program can do is one of these or
   a row of the `prim_op` table above it.
2. **`M06_Typing.fst`, `infer`.** The whole type system. Three of its cases are
   interesting and the rest look up a signature.
3. **`M04_Effects.fst`, the `handler` record** (~line 300). One record. `M10`'s
   job is to show that this is simultaneously an effect handler, a typeclass
   dictionary, a class method table, a module and a Dictionary frame.

If those three read as small, that is the result, not an accident — and §3
below is where the design decisions that made them small are listed.

## 0a. If you have an afternoon

`M01` → `M02` → `M03` → `M05` → `M06`, straight through. They are ordered so
dependency order and reading order coincide, and each is short. Then `M04` and
`M07` together, since `M07` is mostly `M04`'s free monad applied to `M05`'s
syntax. `M08`–`M11` are skeletons; read their headers and skip the bodies.

---

## 1. The map

| Module | What it fixes | Lines | State |
|---|---|---|---|
| `M01_Kinds` | types (`dtype`), primitives, capabilities | 295 | complete |
| `M02_Stacks` | values, intrinsically typed stacks, the frame combinator | 341 | complete |
| `M03_Signatures` | signatures (`srow`), composition, `unify` | 290 | complete |
| `M04_Effects` | operations, effect rows, the free monad, **the handler record and its fold** | 551 | complete |
| `M05_Terms` | core syntax: `term`, `prim_op`, `resolve_defs` | 481 | complete |
| `M06_Typing` | the judgment, as the total function `infer` | 525 | complete |
| `M07_Denotation` | what a program means: `denote_static` | 827 | defined; T1/T2/T5 discharged |
| `M08_Operational` | the abstract machine | 91 | skeleton — `step`/`run` assumed |
| `M09_Soundness` | progress, preservation, and M07↔M08 agreement | 102 | skeleton — S1–S6 prose |
| `M10_Handlers` | that one construct plays six roles | 268 | H1–H5 prose; the fold itself lives in M04 (D-59) |
| `M11_Staging` | `specialize`; compile-time and JIT as one operation | 429 | E1/E3 stated; E2 not yet statable |

**`M08` and `M09` being skeletons is deliberate and is not the same gap twice.**
`M08.step` is assumed *in the specification* and **implemented for real** in
`P02_Reference/R02_Machine.fst`, which runs. What is missing is the F\* proof
that the two agree — S5, the bridge theorem. So the machine is not
unimplemented; it is unverified.

There are exactly **four** `admit`/`assume val` in the whole project, all in
P01, and `make admits` prints them:

| Where | What it costs |
|---|---|
| `M08.step`, `M08.run` | the machine is specified in P02 and assumed in P01; S5 is the missing link |
| `M09.state_typed` | needs `M08.step`'s frame representation pinned down |
| `M11.specialize_typed` | E1 — that a residual is still well typed |

P02 and P03 have none.

---

## 2. The five types everything is built from

Learn these and the rest is notation.

### `M01.dtype` — what a value can be

```fstar
| TPrim : prim -> dtype                       // i64, bool, str, f64, …
| TSeal : nom_id -> list cap -> list dtype -> dtype
| TSum  : list (list dtype) -> dtype
| TName : nom_id -> dtype                     // forward reference to a declaration
| TBox  : dtype -> dtype                      // owning pointer
| TRc   : dtype -> dtype                      // shared pointer
```

Six constructors, and the two absences are the design:

- **There is no product type.** A product is a *stack segment* — a `list
  dtype` — and `TSeal` is what turns a segment into one denotable value with a
  nominal identity. "A class instance is a sealed segment" (D03 §3) is this
  line, not a metaphor.
- **There is no function type**, because there are no runtime function values
  (D-07). A `{}` block is syntax consumed by `THandle`, `TTry` or
  `TSpecialize`, and never reaches the value stack.

`TSum` *is* primitive, and the asymmetry is forced: a stack has a statically
known shape, so something whose shape differs per branch cannot be a segment.

Capabilities (`M01.has_cap`) are where linearity lives. `TSeal` carries its own
capability list, so a sealed type may *drop* capabilities its representation
happens to have — that is what makes linearity opt-in (D-08) rather than a
whole-language mode. `TBox` and `TRc` have neither `Copy` nor `Drop`; they are
the linear types.

### `M02.value` / `M02.vstack` — the stack, indexed by its shape

```fstar
noeq type value : dtype -> Type = …
and       vstack : list dtype -> Type = …
```

The index is the point. "The stack has the shape the signature says" is not a
theorem here but a property of the representation, so most of what a
soundness proof normally has to establish is unstateable-otherwise.

**The convention, relied on everywhere:** the *head* of the index list is the
*top* of the stack. So a signature `(pre -- post)` at row `r` denotes
`vstack (pre @ r) -> vstack (post @ r)`, and the row is the **tail** — the part
further from the top. Surface signatures read the other way (Forth order, top
on the right) and elaboration reverses them. State the convention at every
boundary; the abandoned draft got this wrong in a way that took a while to see.

The **frame property** — a word does not disturb the stack beneath it — is
proved once, about the `frame` combinator at the bottom of `M02`, and every
word inherits it. The abandoned draft made it a per-word obligation and drowned.

### `M03.srow` — a signature

```fstar
type srow = { pre : seg; post : seg }
```

Implicitly row-polymorphic: `∀r. vstack (pre @ r) -> vstack (post @ r)`. The
row variable is never written (D-04).

`M03.compose` is the whole of "type inference" in a concatenative language:
inference *is* signature composition, which is why `M06` is 500 lines and not
5,000, and why an incremental language server is realistic. `M03.unify` is
prefix matching over concrete segments — **not** a unifier in the
Hindley–Milner sense — which is what D-31/D-77 mean by "no unifier".

`M06.impl_frame` and `M06.sig_frames` are the same question asked twice: does
what a term *does* frame to what is *claimed* of it? At the empty state segment
it is the check on a written signature; at a non-empty one it is the check on a
handler implementation threading state. One rule, two callers (D-84).

### `M04.free` — the meaning of an effect

```fstar
| Pure : vstack a -> free env a
| Op   : op:op_id -> arg:vstack … -> k:(… ^-> free env a) -> free env a
```

A program's meaning is a *syntax tree of operation calls*, not an
interpretation of them. Handlers interpret the tree. The continuation is
`FStar.FunctionalExtensionality.(^->)` rather than a plain arrow (D-51), which
is what lets the monad laws be proved rather than assumed.

### `M04.handler` — the one construct

```fstar
noeq type handler (env:sig_env) (eff:eff_id) (st:seg) = {
  h_ops : op:op_id -> op_impl env st (op_of env op);
}

type op_impl env st o = vstack (st @ o.op_pre) -> free env (st @ o.op_post)
```

Read `op_impl` closely, because two decisions are visible in it:

- **No continuation argument.** An operation call runs an implementation which
  *returns* (D-36). Nothing is captured, ever. "Every effect is reentrant" is
  the *installed-frame* property — `M04.handle`'s forwarding clause keeps the
  handler wrapped around the tail — not deep-handler semantics.
- **`st` is on top**, and threaded through: `st @ op_pre` in, `st @ op_post`
  out. That is what makes a handler a **class**: `st` is the instance
  representation and each implementation is a method over it (D-46). A
  stateless handler is `st = []`, so nothing needs a separate rule.

`h_ops` is a function field, which every *extractable* module is forbidden
(D-20/D-45). It is confined to the denotational side; nothing outside the
specification constructs a `handler`. De-closuring it needs an existential
rather than a list, because the table is dependently typed per operation — this
is the one place D-45 could not reach, and it is recorded as the obstacle in
N02 Q-18.

---

## 3. Where each design claim is cashed out as a definition

This is the section to check the project's rhetoric against.

| Claim | The definition that is it |
|---|---|
| **D-01.** Effects, interfaces, traits, classes, modules and the Dictionary are one construct | `M04.handler` — one record. `M10` is the argument that all six readings are it; `M04.eff_dict = 0` makes the Dictionary literally an effect (D-63) |
| **D-02.** Compile-time specialization and runtime JIT are one operation | `M11.specialize`. `E06.discharge_dict` runs it at elaboration; `R02`'s handler chain runs the same rewriting at run time. `demos/03` shows the two giving the same answer |
| **D-06.** Sums primitive, products segments | `M01.dtype` — `TSum` present, no product former; `TSeal` over a `list dtype` |
| **D-07.** Code first-class, functions not | `M05.term` has no lambda and `M01.dtype` no arrow. Blocks are arguments to `THandle`/`TTry`/`TSpecialize` |
| **D-08.** Linearity is opt-in | `M01.has_cap`; `TSeal` carrying its own `list cap` |
| **D-04.** Signatures implicitly row-polymorphic | `M03.srow` has no row field; `M02.frame` recovers it |
| **D-55.** The core is structure, not vocabulary | `M05.term`; every intrinsic is a `prim_op` row, never a constructor. D-55 says *seven* constructors and `M05` now has eight — `TTry` arrived with D-71 and `TCase` became `TDispatch`; the decision's count is stale, its rule is not |
| **D-60.** A word call and an operation call are the same node | `M07`'s `TWord` clause is `M04.Op`; `M06.wenv` has **one** signature table, not two |
| **D-68.** There is no branching construct | `TDispatch` — `case` is `THandle e [] TNil branches (TDispatch …)`. `if` is a macro over that |
| **D-36.** Handlers are stateful objects | `M04.op_impl` — no continuation parameter |

**`TDispatch` is the one worth staring at.** The core has *no* branch. A `case`
is a handler whose implementations are the branches and whose scrutinee
performs the operation its tag selects. So the branching construct and the
effect construct are also one thing, and `M06.infer_branches` and
`M07.denote_case` were **deleted** rather than rewritten when this landed.

---

## 4. The theorems, and what is actually proved

Labels are the ones used in the files. `make verify` passes on all of them
because an unproved one is *stated in prose*, never stubbed as a `Lemma True` —
a rule worth knowing before you read a header and assume the worst.

**`M07`, the denotation — T1–T6**

| | | Status |
|---|---|---|
| T1 | the empty program is the identity | **discharged** (`thm_t1`), definitional |
| T2 | juxtaposition denotes composition | **discharged** (`thm_t2`) — the `TSeq` clause *is* the call, so the content moved into `M03.lemma_compose_assoc` and the `unify` lemmas, which are proved |
| T3 | naturality in the row (framing) | stated |
| T4 | purity is real: an empty row performs no operation | stated |
| T5 | effect-row soundness | **repaired**, true as originally written — it was *false for three commits* and nothing could tell, because it was a comment (D-63) |
| T6 | capability soundness | cannot yet be stated; it is a statement about `M02` |

T5's history is the argument for mechanizing at all, and the header says so.

**`M09`, soundness — S1–S6.** All prose. S5 (agreement between `M07` and
`M08`) is the one that matters: it is what makes the reference interpreter a
witness for the semantics compiler correctness is stated against. Without it
the two halves of the project are unrelated artefacts.

**`M10`, handlers — H1–H5.** All prose. H1 (handling discharges the effect) is
the case every induction in `M07`/`M09` needs.

**`M11`, staging — E1–E6.** E1 (a residual is still well typed) and E3 (a
fully static row leaves nothing behind) are stated; E1's conclusion is
`sig_frames`, not equality, because a residual may be usable in *more* contexts
than the original (D-84). **E2, the zero-cost theorem, is not yet statable** —
`M07.denote_static` excludes `TSpecialize` precisely because E2 is stated
against `denote_static`, so defining it there would be circular. That is a
permanent boundary, not a gap. E7 was **withdrawn** (D-76).

---

## 5. Reading F\* in this project

Five things that will otherwise cost you an hour each.

- **`*` is the tuple constructor**, not multiplication, unless `FStar.Mul` is
  open. The codebase uses `&`. Getting this wrong produces "expected Type, got
  int", which does not sound like what it is.
- **Mutual recursion needs an explicit lexicographic measure.** The pattern,
  used in `M01`, `M05` and `M06`:
  ```fstar
  let rec f (t:term)      : Tot bool (decreases %[(term_size t <: nat); 0]) = …
  and     g (ts:list term): Tot bool (decreases %[terms_size ts;        1]) = …
  ```
  Rank orders `list(1) > element(0)`; it is acyclic because every
  element-to-list edge strictly decreases size.
- **P01 has no `.fsti` on purpose** (D-22). An interface makes a definition
  opaque unless the interface *gives* it, and `M07.denote` needs
  `infer env TNil` to reduce — so interfacing `M06` breaks the build. P02 has
  interfaces; P01 must not.
- **Every `admit` and `assume val` carries a comment** saying what discharging
  it requires. `make admits` is meant to read as an inventory.
- **`noeq`** appears on most type declarations because `prim_rep` may be an
  abstract float type, which has no decidable equality.

---

## 6. What sits on top

`P01` is the specification. Two things are built from it and both run:

- **`P02_Reference/` R01–R06** — the reference interpreter. `R02_Machine` is
  the real `M08.step`. Extracts to OCaml; `make interp` runs it. It is held to
  a **first-order subset** — no closures, no higher-order functions, no
  function-typed record fields — because each would need a catcat image that
  does not exist, and the mapping in `R06_SelfHost` §2 has to stay total.
- **`P03_Elaboration/` E01–E06** — lexer, parser, elaborator, REPL. `make
  catcat` builds it. This is where the surface language lives, and
  `DOCS/U01`–`U03` describe *it*, not this directory.

The relationship worth keeping straight: **`P00_Design/` describes the language
as designed, `DOCS/` describes the language as it runs, and `P01` is what is
actually proved about the part in the middle.** All three drift. `DOCS/` files
carry a commit stamp so a reader can tell how stale one is; this file does too,
at the top.

---

## 7. Where to look when you want to change something

| You want to… | Start at |
|---|---|
| add a type | `M01.dtype`, then `has_cap`, `wf_dtype`, `R04.erase_value`, and every renderer. Consider a `prim_rep` row instead — that is what `str` did (D-65) |
| add an operation | a `prim_op` row in `M05`, its rule in `M06.prim_sig`, its meaning in `M07.prim_den` and `R02.apply_primop`. Never a `term` constructor |
| add a term constructor | don't, without reading D-55 first. It touches `M05` (×2), `M06`, `M07`, `R02`, `E05` and `R06`'s mapping table |
| change surface syntax | `P03_Elaboration/`, and check D-30 (no lookahead, lexer or parser) before adding any case |
| add a library | `NOTES/N04_Roadmap.md` §4.1 — the answer is an F\* module that emits `M05.term`, not a core change |
| understand why a thing is the way it is | `NOTES/N01_Decisions.md`. It is long, and it is the reason this project does not re-litigate |
