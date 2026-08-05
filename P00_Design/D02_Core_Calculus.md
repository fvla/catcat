# D02 — The Core Calculus

The core is deliberately tiny. It has one sequencing construct (juxtaposition),
no binding forms, no closures, and no locals. Everything the surface language
offers beyond this is elaborated away before a program reaches here (D05).

Mechanized in [M01_Kinds](../P01_Specification/M01_Kinds.fst) through
[M07_Denotation](../P01_Specification/M07_Denotation.fst).

---

## 1. Types

```
prim  ::= i8 | i16 | i32 | i64 | u8 | u16 | u32 | u64 | f32 | f64 | bool | unit

dtype ::= TPrim prim
        | TSeal nom_id [cap] seg      -- nominal type over a representation
        | TSum  [seg]                 -- tagged union, one segment per variant
        | TName nom_id                -- incomplete type: forward reference to a declaration
        | TBox  dtype                 -- owning unique pointer   (Rust Box)
        | TRc   dtype                 -- shared refcounted ptr  (Rust Rc)

seg   ::= [dtype]                     -- a stack segment; also "tuple"
```

**A segment is the product type.** There is no separate tuple or struct former:
a product of `i64` and `bool` is the segment `[i64, bool]`, which is simply two
adjacent stack slots. The draft's claim that type-access erasure removes the need
for a product type is correct, with one amendment — you still need a way to make
a segment into *one* denotable thing, which is `TSeal`.

**`TSeal n caps repr`** is a nominal type named `n`, represented by segment
`repr`, exposing capability set `caps`. Sealing does three jobs at once:

1. Turns a multi-slot segment into a single slot for typing purposes.
2. Gives it a nominal identity, so two structurally identical classes differ.
3. **Narrows capabilities** — the sealed type may expose fewer than its
   representation has. This is what makes a linear `Counter` over a copyable
   `i64` an actual guarantee (D03 §5).

`TSeal` carries its representation *inside the type* rather than in a side table.
This keeps M01–M07 entirely environment-free, which in turn keeps the denotation
a plain function instead of one parameterized by a signature context. Name
resolution reintroduces an environment in M06, where it belongs.

**`TName n`, `TBox t`, `TRc t`** are what make recursion expressible. `TName n`
is an *incomplete type*: an explicit forward reference to a declaration `n`,
resolved nowhere in M01–M02. `TBox t` and `TRc t` are pointers — an owning
unique pointer and a shared refcounted one, Rust's `Box` and `Rc`, deliberately
named the same. Recursion is legal only **through a pointer**, exactly as in
Rust and C++:

```
List = TSum [ [] ; [TPrim PI64; TBox (TName list_id)] ]
```

A well-formedness predicate `wf : dtype -> bool` (M01) rejects a bare `TName`
not behind a pointer — the grammar above does not exclude `TName n` on its
own, so `wf` is what keeps layout finite, exactly as C++ rejects
`struct S { S field; }`. `wf` is checked at every place a type reaches a slot
boundary (`PBoxNew`, `PRcNew`, `PRoll`/`PUnroll` in M06).

> **Resolved: recursive types via pointer indirection.** `dtype` used to be
> entirely structural and finite, so `List[#T] = Nil | Cons #T List[#T]` was
> inexpressible — found by attempting the catcat encoding in
> [R06_SelfHost](../P02_Reference/R06_SelfHost.fst) §3. `TName`/`TBox`/`TRc`
> fix it, with the pointer-indirection rule above. Two properties make the
> fix cheap rather than merely possible:
>
> 1. `dtype` **values** stay finite trees, because `TName` is a leaf. The
>    recursion lives at the declaration level, not in the syntax tree, so
>    there is no positivity obligation and no termination problem.
> 2. **No type environment is needed in M01/M02**, because a pointer's
>    capabilities do not depend on its pointee: `has_cap` never looks through
>    `TBox`/`TRc`, so it never reaches a `TName`, so it never has to resolve
>    one. An environment is needed only to *unfold* a name, which typechecking
>    `PUnroll` needs and the runtime does not.
>
> See R06 §3 for the fix as found and what remains, and D06 §5 for where it
> sat in the schedule.

**`TSum variants`** is the primitive tagged union; variant `i` carries segment
`index variants i`. Layout is a tag plus the max variant size.

---

## 2. Stacks

**Convention, fixed globally: the head of the index list is the top of the
stack.** A signature `(a -- b)` at row `r` denotes
`vstack (a @ r) -> vstack (b @ r)` — the row is the *tail*, i.e. the part further
from the top.

> Surface signature notation follows the Forth convention and reads
> bottom-to-top, with the top of the stack on the **right**. The core's index
> lists are top-first. Elaboration reverses them. This mismatch is deliberate —
> Forth programmers read `( a b -- c )` with `b` on top — but it is exactly the
> kind of detail that produces silent bugs, so it is stated here and again in
> D05 §2.

A stack is an inductive family indexed by its shape:

```fstar
noeq type value : dtype -> Type =
  | VPrim : #p:prim -> prim_rep p -> value (TPrim p)
  | VSeal : n:nom_id -> caps:list cap -> #repr:seg -> vstack repr
          -> value (TSeal n caps repr)
  | VSum  : #variants:list seg -> tag:nat { tag < length variants }
          -> vstack (index variants tag) -> value (TSum variants)

and vstack : seg -> Type =
  | VNil  : vstack []
  | VCons : #t:dtype -> #ts:seg -> value t -> vstack ts -> vstack (t :: ts)
```

Well-typedness is structural: an ill-shaped stack is not merely rejected, it is
*unrepresentable*. This is the change that dissolves the difficulties recorded
in D01 §3.4.

The entire structural burden is two lemmas:

```fstar
val vappend : #a:_ -> #r:_ -> vstack a -> vstack r -> vstack (a @ r)
val vsplit  : a:seg -> #r:_ -> vstack (a @ r) -> vstack a & vstack r

lemma_vsplit_vappend : vsplit a (vappend x y) == (x, y)
lemma_vappend_vsplit : let (x,y) = vsplit a s in vappend x y == s
```

---

## 3. Framing: the categorical core

```fstar
let frame (#a #b:seg) (r:seg) (f: xform a b) : xform (a @ r) (b @ r) =
  fun s -> let (x, y) = vsplit a s in vappend (f x) y
```

`frame` is the tensor `f ⊗ id_r` of the monoidal category the language denotes
into. Everything the draft wanted to say about words not disturbing the rest of
the stack is said here, **once**:

| Law | Meaning |
|---|---|
| `frame r f (vappend x y) == vappend (f x) y` | `f` runs on the top; the row passes through untouched. |
| `frame r id == id` | framing preserves identities |
| `frame r (g ∘ f) == frame r g ∘ frame r f` | framing preserves composition |

The last two say `frame r` is a **functor**. That is what licenses compiling a
word once and reusing it at every stack depth, rather than once per depth — a
practical consequence, not decoration.

*(The unit law `frame [] f == f` is omitted from M02: `a @ []` is only
propositionally equal to `a`, so stating it needs a transport and it says nothing
the application law does not. It appears at signature level in M03, where it is
type-correct.)*

---

## 4. Signatures and composition

A signature is **implicitly row-polymorphic**:

```fstar
type srow = { pre : seg; post : seg }     -- means  forall r. pre @ r ==> post @ r
```

The row variable is never written in the core; it is recovered by `frame`. This
is what makes the frame property structural rather than a per-word obligation.

Composition unifies the producer's outputs against the consumer's inputs,
element-wise from the top:

```fstar
let rec unify (b c:seg) : option (seg & seg) =
  match b, c with
  | [], _              -> Some ([], c)     -- consumer needs more, from below
  | _, []              -> Some (b, [])     -- producer left surplus, stays put
  | t1 :: b', t2 :: c' -> if t1 = t2 then unify b' c' else None

let compose (f g:srow) : option srow =
  match unify f.post g.pre with
  | None                  -> None
  | Some (b_rest, c_rest) ->
    Some ({ pre = f.pre @ c_rest; post = g.post @ b_rest })
```

The placement of the residuals is the part the draft got wrong:

- When the **producer's outputs run out**, the shortfall must be drawn from
  *below* the producer, so it belongs in the composite's **`pre`**.
- When the **consumer's inputs run out**, the surplus stays on the stack beneath
  whatever the consumer produces, so it belongs in the composite's **`post`**.

At most one of the two is non-empty (`lemma_unify_disjoint`).

**Worked example.** `f : ( -- i64 )` composed with `g : ( i64 bool -- str )`.
In core (top-first) terms: `f = {pre=[]; post=[i64]}`, `g = {pre=[i64,bool]; post=[str]}`.
`unify [i64] [i64,bool] = Some ([], [bool])`, so the composite is
`{pre = [] @ [bool] = [bool]; post = [str] @ [] = [str]}` — the `bool` the
consumer still needed is now demanded of the composite. Reading in surface
notation: `( bool -- str )`.

Signatures form a **category**: identity `{[],[]}` with the unit laws proved, and
associativity stated. *(Associativity is currently admitted — see §8.)*

---

## 5. Terms

**Seven constructors.**

```
term ::= TNil                             -- identity
       | TSeq term term                   -- juxtaposition; the ONLY sequencing form
       | TPrimOp prim_op                   -- an intrinsic; see below
       | TWord word_id                     -- named word OR interface operation
       | TCase [seg] [term]                -- sum elimination, one block per variant
       | THandle eff_id seg term [(op_id, term)] term
       | TSpecialize term                  -- staging; see D04
```

That is the whole of the core's *structure*: identity, composition, naming,
elimination, handling, staging. Its *vocabulary* is a separate, flat table
(D-55), every entry of which is pure and monomorphic:

```
prim_op ::= PLit lit
          | PStack sop                     -- dup / pop / swap / pick / roll
          | PPack   nom_id [cap] seg       -- segment  -> nominal
          | PUnpack nom_id [cap] seg       -- nominal  -> segment (class body only)
          | PInj  [seg] nat                -- sum introduction
          | PBoolSum                       -- bool -> two-variant sum
          | PBoxNew | PBoxOpen             -- dtype each
          | PRcNew | PRcClone | PRcDrop | PRcRead
          | PRoll nom_id dtype | PUnroll nom_id dtype
```

Each entry has a signature (`M06.prim_sig`), a denotation (M07) and a machine
action (`R02.apply_primop`), and nothing else. The split matters because every
induction over `term` in M07 and M09 gets **one** primitive case rather than
twelve, and because a native library (D-56) extends the table without touching
the language.

The invariant that makes the grouping honest: **every primitive is pure.**
`prim_sig` returns no effect row, and `apply_primop` is given neither the
dictionary nor the continuation, so a primitive cannot perform an operation,
call a word, or alter control flow. Anything that could is a `TWord` resolving
to an operation — which is why `print` is not in the table.

Note what is **absent**: no lambda, no application, no let, no local binding, no
closure. Locals (`$x`) elaborate to stack shuffles and the core never learns they
existed. **There is also no conditional** — `PBoolSum` coerces a `bool` to a
two-variant sum and `TCase` does the rest, so branching on a boolean and
branching on a user sum are the same construct (D-33). A dedicated `TIf` would
have needed a second copy of the branch-agreement rule.

### Branch agreement

`TCase`'s branches do **not** need equal signatures. Each is row-polymorphic, so
they agree when there is a common instantiation, computed by `M03.srow_join`:
frame each branch by what the other demanded extra, then require the results to
match. So

```
dup 10 < if { } then { 1 - } endif        -- ( i64 -- i64 )
```

is well typed although one arm is `( -- )` and the other `( i64 -- i64 )`. This
is not a special allowance for conditionals; it is what row polymorphism already
meant, applied to alternatives rather than to sequences. The rule originally
required equality, which made every boolean branch unable to touch the stack —
caught by building `if`, since nothing had ever constructed a `TCase` before.

---

## 6. Quotations are not values

`TCase`, `THandle` and `TSpecialize` take `term` arguments *syntactically*. There
is no constructor that pushes a block onto the value stack.

This is the precise content of D01 §3.2: code is first-class at elaboration time,
but there are no runtime function values. Consequences:

- Every `{}` block has exactly one, statically known consumer, so it is always
  inlinable.
- No heap-allocated environments, hence no closure conversion pass and no GC
  pressure from control flow.
- Runtime code exists only as the *output of* `specialize` (D04) — which is the
  JIT, and is explicitly staged rather than implicit.

---

## 7. Typing

The judgment is `env |- t : s ! row`, presented algorithmically as a **total
inference function** ([M06](../P01_Specification/M06_Typing.fst)).

This is not a shortcut. In a concatenative language, type inference *is*
signature composition: a fold over the term with no unification variables, no
constraint store, and no generalization step. Three rules carry the language:

```
  ------------------------          -- identity
  env |- TNil : {[],[]} ! []

  env |- a : sa ! ea    env |- b : sb ! eb    compose sa sb = Some s
  ---------------------------------------------------------------    -- composition
  env |- TSeq a b : s ! (ea ∪ eb)

  ---------------------------------------      -- lookup
  env |- TWord w : env.w_sig w ! env.w_eff w
```

Everything else looks up or builds a signature. The capability rules are the only
other content:

```
  copyable d                        droppable d
  ---------------------------       ---------------------------
  env |- dup_d : (d -- d d) ! []    env |- pop_d : (d -- ) ! []
```

Rejecting `dup` at a non-copyable type is the *entire* enforcement mechanism for
linearity. There is no separate linear sublanguage.

**Deep access.** `dup`/`pop`/`swap` reach only the top two slots, and no
composition of them can touch a third — so `$x` locals, which compile to
n-deep access, need two more operations:

```
  copyable d
  ------------------------------------------------      -- copy from depth |above|
  env |- pick_above,d : (above d -- d above d) ! []

  ------------------------------------------------      -- move from depth |above|
  env |- roll_above,d : (above d -- d above) ! []
```

Each carries the segment `above` the target rather than a count, which keeps
the rule non-variadic and makes the depth visible in the type. `pick` copies and
is therefore capability-gated exactly like `dup`; `roll` only moves, so it is
not. D05 §3 explains how the elaborator chooses between them.

**Why the LSP goal is realistic.** Because inference is a fold along one spine
with no global constraint solving, re-checking after a keystroke means
recomposing that spine. There is no unifier state to invalidate and nothing to
generalize. This is a property of choosing a concatenative core, and it is the
main practical dividend of that choice.

---

## 8. Denotation

A well-typed program denotes a row-polymorphic effectful stack transformer:

```fstar
type cdenote (env:sig_env) (s:srow) =
  r:seg -> vstack (s.pre @ r) -> free env (s.post @ r)
```

The denotation is **indexed by** the row rather than refined by a property
mentioning it — the single change from the draft's approach that makes framing
definitional instead of an obligation.

Sequencing denotes **Kleisli composition** in the free monad. So the draft's
claim that a program is "a complete composition of functions, without reference
to data" is not a slogan here; it is theorem T2 in
[M07](../P01_Specification/M07_Denotation.fst). That theorem is what licenses
treating any word as a black box given only its signature and effect row — which
is in turn what makes the optimizer's DAG view sound and incremental re-checking
correct.

### Current gaps

All eleven modules verify. The gaps are explicit and inventoried by
`make admits`:

| Location | Gap | Notes |
|---|---|---|
| `M03.lemma_compose_assoc` | admitted | Four-way case analysis on which segment runs out; closes by `append_assoc` and `lemma_unify_disjoint`. **Discharge first** — M07's `denote` needs the same transport. |
| `M04.lemma_fbind_right_id`, `lemma_fbind_assoc` | admitted | True, but need functional extensionality in the `Op` case. Requires restating `free`'s continuation over `FStar.FunctionalExtensionality.(^->)`. |
| `M07.denote` | `assume val` | Definition is mechanical except the `TSeq` transport. |
| `M07` T2–T6 | recorded as obligations | Stated precisely in prose rather than as `Lemma True` stubs, which would prove nothing while looking like content. |
| `M08`–`M11` | skeletons | Types real, theorem statements real, bodies absent. |
