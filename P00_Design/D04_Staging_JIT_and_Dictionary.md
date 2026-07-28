# D04 — Staging, the Dictionary, JIT, and the Reflective Tower

This document specifies the layer carrying the project's two critical goals:
manual JIT and metacompiler functionality. Both come from one operation.

Mechanized in [M11_Staging](../P01_Specification/M11_Staging.fst); the
type-level half is already proved in
[M06_Typing](../P01_Specification/M06_Typing.fst).

---

## 1. Specialization

```
specialize : program -> dictionary -> program
```

`specialize p d` resolves every statically-staged effect of `p` against `d` and
emits a residual program. It inlines statically resolved words, folds `case` on
known tags, erases `pack`/`unpack`, and leaves dynamic operations alone.

Two call sites, one function:

- **Elaboration time.** Monomorphization, inlining, interface resolution. The
  resolved effects are erased, so the abstraction costs nothing at runtime.
- **Runtime**, with `d` built by the running program. This is the **JIT**.

---

## 2. The two-tier Dictionary

The Dictionary is the ambient chain of handlers determining what each word means.
Rebinding is staged, because unstaged rebinding would make a fragment's type
depend on its handler chain and forfeit static typing, separate compilation and
the fast-LSP goal at once (D01 §3.5).

### Static tier (default)

- Resolved during elaboration.
- A handler **must declare which words it overrides and with what signatures** —
  the `interface` block of D03 §1 is exactly this declaration.
- Fully erased. **Costs nothing at runtime**, guaranteed by §4.
- Covers: modules, generics, typeclass/interface dispatch, class methods,
  compile-time reinterpretation.

### Dynamic tier (explicit opt-in)

- Marked at the declaration site; resolution happens at runtime.
- Compiles to handler-frame lookup — an indirect call, the same cost as a
  virtual call.
- Covers: runtime plugin dispatch, effects genuinely not known until runtime,
  and the JIT's own dictionaries.

The two tiers are one mechanism with an annotation, not two mechanisms. In the
core the annotation is `stage ::= SStatic | SDynamic` on each effect-row entry.

### Modules are Dictionary handlers

A module is an interface plus an implementation; `use` pushes a static handler
frame. Consequences:

- One name-resolution mechanism for the whole language.
- Module-level reinterpretation is free: swapping an entire `math` module for a
  SIMD one is *pushing one frame*, not a separate feature.
- `::` namespacing (D05 §4) is lookup in that chain.

---

## 3. Worked example: the SIMD functor

The draft's motivating case. Given

```
define hypot ( f64 f64 -- f64 ) { dup * swap dup * + sqrt }
```

`hypot` uses `*`, `+`, `sqrt` — all resolved through the ambient `Dict`. So a
handler that rebinds those words to SIMD operations, pushed around a call to
`hypot`, reinterprets it wholesale:

```
with simd_f64x4 { hypot }        -- now ( f64x4 f64x4 -- f64x4 )
```

No new language feature is involved: this is a static Dictionary frame, resolved
at elaboration, erased by §4. The result is the same machine code as a
hand-written SIMD `hypot`.

### 3.1 Why functor lifting stays explicit

**Decision: no implicit coercion. Reinterpretation is always written.**

The idea considered was coercing *functions* to match values — given `hypot` at
`f64` and arguments at `f64x4`, implicitly lift the function rather than convert
the values. This is not value casting, and the distinction matters for why it is
rejected.

Lifting a function means changing which `*` and `+` its body resolves to. That is
**instance selection**, and instance selection driven by the argument types is a
search: the checker must consider candidate liftings, and with more than one
applicable functor it must choose. Search is where composition stops being a
table lookup, where inference time becomes input-dependent, and where error
messages degrade — a failure no longer points at one slot but at a rejected set
of candidates.

Speed alone would not have settled this. A fixed table of *value* coercions costs
one lookup per slot during `unify` — O(1) per element, no change in asymptotics —
and the incremental-LSP claim (D02 §7) would survive it comfortably. The
objection is specifically that function-level lifting cannot be reduced to that
lookup.

So reinterpretation is written:

```
with simd_f64x4 {hypot dup *}
```

One line, no search, and the reinterpreted region is visible to a reader.

*(If value-level widening coercions are ever wanted, they are a separate feature
and remain available under three rules: apply only when both types are ground,
be a partial function with chains pre-closed, and never select an overload. A
coercion would also need to be capability-preserving or require `Copy`
explicitly, since one that silently duplicated a linear value would defeat
D03 §5. Nothing in the current design needs this.)*

---

## 4. The zero-cost theorem

This is the requirement stated as non-negotiable: compile-time specialization
must cost nothing at runtime. It is a theorem, not an aspiration.

**E2 — semantic preservation.** For well-typed `t` with row `row`, and `d`
resolving every static effect of `row`:

```
denote (specialize t d)  ==  handle_d (denote t)
```

Specializing is the same as running with the dictionary installed.

**E3 — static effects are erased.** If every entry of `row` is `SStatic` and `d`
resolves it, then `specialize t d` is **pure**: the residual program contains no
effect operations at all.

E3 is the precise form of "compile-time specializations cost nothing at runtime".
It is what licenses building the object model, the module system, generics and
interface dispatch all on the effect machinery *without paying for any of them* —
and it is the theorem to reach for whenever someone suspects the unification of
D03 is too clever to be fast.

**The type-level half is already proved.**
`M06.lemma_static_specializes_to_pure` shows that a fully static row specializes
to an empty row, and `M06.lemma_specialize_row_shrinks` shows specialization
never introduces effects. The semantic half (E2, E3) awaits `M07.denote`.

---

## 5. JIT

**E4 — JIT correctness.** E2 with `d` constructed at runtime.

No separate theorem is required, and that is the entire point. The JIT is correct
because specialization is correct, so there is no second trusted path from source
to machine code — the usual failure mode of JIT compilers, where the interpreter
and the compiled path drift apart, is structurally excluded.

A JIT-ing word is one that calls `specialize` with a runtime dictionary and then
invokes the result. Its effect row records `Compile` as dynamic, which is what
makes the JIT *manual and visible in the type system*, as D01 requires — you can
tell from a signature whether a word may compile code.

---

## 6. The reflective tower

The compiler is written in catcat, generated and verified from F* (D06 §2). Any
portion of it can be embedded in an output executable, and **the binary cost is
opt-in**.

### The effect row drives binary composition

This is the mechanism, and it needs no new machinery: the linker computes what to
embed from the entry point's dependency tree, using the *effect row* the type
checker already produced.

| Requirement | Triggered by | Embedded |
|---|---|---|
| `ReqNone` | no `Compile` effect anywhere | nothing |
| `ReqSpecial` | staged code, no codegen | specializer |
| `ReqCodegen` | dynamic `Compile` | specializer + backend |
| `ReqFull` | `eval`, metacompilation | parser + full pipeline |

A program that never JITs links no compiler stage at all. A program that JITs
integer kernels links the specializer and backend but not the parser. This is
the Lisp-image property with the cost made proportional to use, and it is
`M05.needs_compiler` plus the row, not a separate analysis.

**E5 — stage minimality**: if `stage_required t = ReqNone`, no compiler stage is
reachable, so the linker may omit all of them. This is what makes opt-in cost a
guarantee rather than a usual-case observation.

### Prior art

**"Collapsing Towers of Interpreters"** (Amin & Rompf, POPL 2018) is the closest
existing formal treatment: a tower of interpreters staged so the levels cost
nothing. Read it before finalizing this document. **Terra** is the closest
working system — Lua staging a low-level compiled language with LLVM JIT — and is
worth studying for what the staging boundary feels like in practice.

Where catcat diverges from both: the staging annotation lives in the *effect
row*, which is also the interface, module and object mechanism. So the tower is
not a separate construct layered on the language; it is the same construct
resolved later.

**E6 — tower collapse.** Specializing a catcat interpreter, written in catcat,
against a fixed program yields a residual equivalent to specializing that program
directly — the first Futamura projection. Not needed for the language to work,
but it is the theorem that makes the metacompiler goal precise, and the natural
checkpoint before committing to self-hosting (D06 §2).

---

## 7. Design risk: E3 needs a competent optimizer

The honest one: **§4's erasure must hold in the real compiler, not just the
spec.** E3 says the residual program contains no effect operations. It says
nothing about dead code, redundant moves, or stack traffic. A pure but bloated
residual means the language is semantically zero-cost and practically slow.

Efficiency therefore depends on the optimizer clearing a basic bar. For this
language family the bar is specific, and one pass dominates:

1. **Stack-to-SSA conversion.** Inlining plus locals elaboration (D05 §3)
   generates enormous `dup`/`swap`/`pop` traffic — it is the characteristic
   output shape of a concatenative front end. Converting stack traffic into
   value dataflow is what makes everything downstream work; Factor and Kitten
   both live or die on it. Without this pass the residual is pure and slow no
   matter what else is implemented.
2. **Dead code elimination** over the resulting dataflow, which is what actually
   removes the specialized-away abstraction's remains.
3. **Copy propagation / slot coalescing**, which removes what SSA conversion
   leaves behind.
4. **Constant folding**, mostly free once staging has already resolved the
   static tier.

Passes 2–4 are standard and cheap *given* pass 1. Pass 1 is the investment.

Mitigation, beyond building those: make E3 a *testable* property early. Once P02
exists, a differential harness comparing `specialize`d output against
hand-written equivalents on a benchmark set catches divergence long before the
backend work in P04. The theorem constrains the design; the harness constrains
the implementation. Both are needed, and neither substitutes for the other.
