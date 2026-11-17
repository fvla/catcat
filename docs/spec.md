# catcat specification

catcat is a statically stack-typed concatenative language built on one construct, the effect handler. This document specifies its two lowest layers:

- **Layer 0, the kernel:** stack shapes, four structural term forms plus `run`, and their meaning.
- **Layer 1, the bootstrap language:** a reader, three types, a handful of forms and a primitive table, all defined by translation to the kernel.

The Lean sources under `Catcat/` implement both layers and are the reference. Where this document and the sources disagree, the sources win. Notation here is Lean-flavoured pseudocode.

Two rules shape everything below.

- **Design rule.** One kernel construct should carry as many language features as possible. Both layers stay as small as they can, in features and in the size of their definition.
- **Placement principle.** A piece of code is given its meaning at the place it is used, so the handlers around that place apply to it.

---

## Layer 0: the kernel

The kernel names no base type, no primitive and no effect.

### Parameters

```lean
B      : Type                  -- base types
val    : B → Type              -- their values
Name   : Type                  -- operation names, with decidable equality
code   : Sig → B               -- the type of code values with a given signature
decode : val (code s) → Term   -- how a code value becomes a term; infer (decode v) = s
```

### Shapes and terms

```lean
Seg := List B                                        -- head = top of stack
Sig := { pre : Seg, post : Seg }                     -- ∀ r, pre ++ r → post ++ r
Op  := { name : Name, pre : Seg, outs : List Seg }   -- one result segment per outcome

Term ::= nil
       | seq    Term Term
       | op     (o : Op) (branches : List Term)      -- one branch per outcome
       | handle (rec : Bool) (st : Seg) (clauses : List (Op × Term)) (body : Term)
       | run    (s : Sig)                            -- execute a code value here
```

An operation label carries its own signature. An ordinary operation has one outcome and the branch `nil`. An operation with several outcomes is how the kernel branches: the operation picks an outcome and the matching branch runs.

### Typing

`infer : Term → Option Sig` and `free : Term → Set Op` are both structural.

| Term | Signature | Free operations |
|---|---|---|
| `nil` | `[] → []` | `∅` |
| `seq t u` | `compose s_t s_u` | `free t ∪ free u` |
| `op o us` | `o.pre ++ P → Q`, where each branch, entered with `o.outs[i]`, is framed to the deepest and must then equal `P → Q` | `{o} ∪ ⋃ free uᵢ` |
| `handle rec st cl b` | `st ++ s_b.pre → st ++ s_b.post` | `(free b \ dom cl) ∪ ⋃ free cᵢ`, minus `dom cl` again if `rec` |
| `run s` | `code s :: s.pre → s.post` | not known until run |

`compose` matches the first signature's output against the second's input. Whatever is left over on either side is carried through.

Rules for `handle`:

1. Every handled operation has exactly one outcome.
2. A clause for `o` has signature `st ++ o.pre → st ++ o.outs[0]`.
3. A clause's own operations are handled by the handlers outside this one. With `rec`, also by this one.
4. `rec` requires `st = []`.

The effect row of a term is `free t`. It is computed, never declared.

### Meaning

```lean
inductive Free (a : Seg)
  | pure : Stack a → Free a
  | op   : (o : Op) → Stack o.pre → ((i : Fin o.outs.length) → Stack o.outs[i] → Free a) → Free a

⟦nil⟧                 = pure
⟦seq t u⟧             = ⟦t⟧ >=> ⟦u⟧
⟦op o us⟧ r (x ++ y)  = op o x (fun i res => ⟦uᵢ⟧ (res ++ y))
⟦run s⟧ r (c :: x)    = ⟦decode c⟧ r x                                 -- not structural
⟦handle rec st cl b⟧ r (s ++ x ++ y) = frame y (go s (⟦b⟧ [] x))

go s (pure v)   = pure (s ++ v)
go s (op o x k) =
  if (o, c) ∈ cl then
    if rec then go [] (⟦c⟧ [] x >>= k 0)                               -- not structural
    else        ⟦c⟧ [] (s ++ x) >>= fun (s' ++ res) => go s' (k 0 res)
  else op o x (fun i res => go s (k i res))
```

- Everything is structural except the two marked lines. An evaluator needs fuel at `rec` and at `run`, and nowhere else.
- `run` puts the code's term where the `run` is, so the placement principle holds for code values.
- A handled block is given its meaning on its own stack and framed afterwards, so a handler never has to commute with framing.

### Models

A **model** interprets a set of operations: arguments in, an outcome and its results out. The **root model** is whatever is left to interpret a program's free operations.

A program with no `run` is closed when `free t` lies inside the root model's set. Code executed by `run` can perform an operation that nothing handles; that is a runtime error.

### Laws

| | Law |
|---|---|
| K1 | Signatures form a category under `compose` |
| K2 | `Free` is a monad |
| K3 | Sequencing is Kleisli composition; framing is natural |
| K4 | `go` distributes over bind, threading the state |

None is proved yet. None depends on `run`.

### What the kernel covers

| Feature | How |
|---|---|
| Dynamic variable | a handler with a one-cell state, a read clause and a write clause |
| Free variable | an unhandled operation |
| Recursion | a `rec` handler placed around the call site |
| Late-bound behaviour | an operation, handled wherever the caller chooses |
| Reinterpretation | an inner handler shadows an outer one |
| Mocked I/O, trusted models | a handler in place of the root |
| Conditional, data elimination | an operation with several outcomes |
| Effect row | `free t` |
| Word definition | nothing: lowering splices the body at each call site |

---

## Layer 1: the bootstrap language

### Reader

The reader splits its input on whitespace and does nothing else.

- A token is a bracket, an integer literal (digits with an optional sign), or a word (anything else).
- A bracket is a token only when it stands alone: write `{ 5 + }`, never `{5 +}`.
- A lone `#` starts a comment that runs to the end of the line.

| Bracket | Meaning |
|---|---|
| `( … )` | a signature |
| `[ … ]` | a syntax object |
| `{ … }` | a code block |

### Types

| Type | Values |
|---|---|
| `int` | unbounded integers |
| `Syn` | syntax objects: immutable sequences of tokens and bracketed groups |
| `Code ( sig )` | code blocks with that signature |

A signature is written bottom to top, the top of the stack on the right: `( int Syn -- int )`.

Every value can be copied and dropped. A `Code` value is represented by its syntax, and no operation turns it back into a `Syn`.

### Forms

Each form lowers to kernel terms. `rest` is the remainder of the enclosing block.

| Surface | Lowering |
|---|---|
| `5` | `op (lit 5)` |
| `[ … ]` | `op (lit …)`, a `Syn` |
| `{ … }` | `op (lit …)`, a `Code` whose signature is inferred |
| `( sig ) { … }` | the same, with the signature given |
| `run` | `run s`, with `s` read off the `Code ( sig )` on top of the stack |
| `w`, a primitive | `op w` |
| `w { a } { b } …`, a primitive with several outcomes | `op w [a, b, …]` |
| `define w { c } rest` | in `rest`, each `w` is replaced by `c` |
| `define w ( sig ) { c } rest` | in `rest`, each `w` is replaced by `handle true [] [(w, c)] (op w)` |
| `let [ x ] rest` | `handle false [T] [(x, pick 0), (x!, drop)] rest`, then `drop`; `T` is the type on top of the stack |
| `x`, a variable in scope | `op x` |
| `set [ x ]` | `op x!` |

Notes:

- **Words are spliced.** A word defined without a signature has no type of its own. Its body is lowered again at each call site, against the stack found there. A definition is therefore checked where it is used, and it may use the variables in scope at the call.
- **Recursion needs a signature.** Inside its own body a recursive word is an operation, handled by the `rec` handler that wraps the call site. Mutual recursion is not supported yet.
- **Scope.** `define` and `let` reach to the end of the enclosing block. A body sees only definitions made before it.
- **Variables.** `let` takes the value on top of the stack as the initial value. By convention a variable is named `$*x`. A code block may only mention a variable that is in scope where the block is written; when the block runs, the innermost binding at that moment is used.
- **Inferred code blocks.** The inputs of `{ … }` are inferred from the operations in it. That fails for an operation whose signature depends on the stack (`drop`, `pick`, `roll`, `let`, `run`) when it would reach below the block's own values. Give such a block a signature.

### Primitives

| Group | Operations | Signature |
|---|---|---|
| Stack | `pick [ n ]` | copies the `n`-th value from the top (0 is the top) |
| | `roll [ n ]` | moves the `n`-th value to the top |
| | `drop` | removes the top |
| Integer | `+` `-` `*` `/` `%` | `( int int -- int )` |
| | `<` `=` | `( int int -- int )`, giving 1 or 0 |
| Branch | `if { a } { b }` | `( int -- )`; non-zero runs `a`, zero runs `b` |
| Syntax | `len` | `( Syn -- int )` |
| | `slice` | `( Syn int int -- Syn )`, items from the first index up to the second; out-of-range indices are clamped |
| | `cat` | `( Syn Syn -- Syn )` |
| | `wrap` | `( Syn -- Syn )`, one item holding the input as a group |
| | `int>syn` | `( int -- Syn )` |
| | `eq` | `( Syn Syn -- int )` |
| | `view { a } { b } { c } { d }` | `( Syn -- … )`, four outcomes, below |
| Code | `compile ( sig ) { a } { b }` | `( Syn -- … )`; if the syntax lowers at `sig`, `a` runs with the `Code` on the stack, otherwise `b` runs |
| Host | `emit` | `( int -- )`, writes the character with that code |

Division truncates toward zero. `a / 0` is 0 and `a % 0` is `a`, so every integer operation is total.

`view` takes a syntax object apart:

| Outcome | When | Branch receives |
|---|---|---|
| 1 | a single integer token | the `int` |
| 2 | a single word token | the `Syn` unchanged |
| 3 | a single group | its contents, a `Syn` |
| 4 | anything else | the `Syn` unchanged |

All branches of a branching primitive must leave the same stack.

### Example

```
define fact ( int -- int ) {
  pick [ 0 ] if { pick [ 0 ] 1 - fact * } { drop 1 }
}
5 fact
```

lowers to

```
lit 5 ; handle true [] [ (fact, C) ] (op fact)
  C = pick0 ; op if [A, B]
  A = pick0 ; lit 1 ; - ; op fact ; *        -- [int] → [int]
  B = drop ; lit 1                            -- [int] → [int]
```

`if` consumes the flag. Both branches are `[int] → [int]`, so they join with no framing, and `C` has the declared signature.

### Running a program

A program is a sequence of forms starting from an empty stack. Its output is whatever `emit` wrote, followed by the final stack, bottom first.
