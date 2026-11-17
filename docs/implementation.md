# Implementation notes

Explanations that are too long for a code comment. The definitions are in [spec.md](spec.md); this file is about how the Lean sources realize them.

## Conventions

- **Stack order.** Every list of types or values is top-first. Source signatures are written the other way round, bottom to top, and are reversed when parsed.
- **Short code.** Spec code is kept short. When a definition needs more explanation than a line or two, the explanation goes here.
- **Comments** give a reason or a non-obvious invariant. They never restate the code.

## Kernel (`Catcat/Kernel`)

| File | Contents |
|---|---|
| `Term.lean` | `Sig`, `Op`, `Term` |
| `Typing.lean` | `Sig.compose`, `Sig.join`, `Term.infer`, `Term.free` |
| `Eval.lean` | `Free`, `den`, `handler`, `Free.exec` |

The kernel is generic in the base types `B`, the operation names `N` and the values `V`.

### Differences from the spec's presentation

- **One value type.** The spec indexes stacks by their type. The implementation uses plain `List V` and checks types separately with `Term.infer`. The typed form is what the laws K1–K4 will be stated for.
- **`Free.stuck`.** With untyped stacks an evaluator can get stuck (an empty stack, no fuel), so `Free` has a third constructor for that.
- **`Free.later`.** A fourth constructor that means `next ()`. A recursive handler returns it before re-handling a clause, so control goes back to `exec` between recursive calls. Without it a word that calls itself first thing would recurse natively once per call and overflow the stack long before the fuel ran out.
- **No framing step.** The spec gives a handled block its meaning on its own stack and frames the result. The implementation hands the block the whole stack below the handler's state. For a well-typed block the two agree, because the block cannot reach below its own inputs.
- **Continuation-passing.** `den t` takes the stack and the rest of the computation, instead of returning a tree to be bound to the rest. This is the spec's `>=>` with the binds fused away. Without it a loop of `n` iterations would cost `n²`, since each iteration would wrap one more bind around everything after it.

### Fuel without a termination proof

Two calls are not structural: re-handling a recursive clause's operations, and giving a meaning to a decoded code value. Everything else recurses on a subterm.

Each non-structural call is passed in as a function. `handlerStep` takes `reenter`, and `denStep` takes `again`. Both are then structurally recursive, on the computation and on the term respectively. The wrappers `handler` and `den` recurse on the fuel and pass themselves in with one unit less:

```lean
def den decode : Nat → Term → Den
  | 0        => denStep decode (fun _ _ _ => .stuck "out of fuel") 0
  | fuel + 1 => denStep decode (den decode fuel) (fuel + 1)
```

So fuel is spent exactly where the spec says, and Lean accepts every definition without a hand-written termination argument.

### `handlerStep`

It walks a computation that may perform operations.

- An operation with no clause is passed outward, with the handler re-installed on its continuation.
- A clause of a plain handler runs with the state on top of the arguments. Its own operations are emitted as they are, which puts them outside this handler. When it finishes, the handler resumes on the continuation with the new state.
- A clause of a recursive handler runs on the arguments alone, and `reenter` handles what it produces.

## Layer 1 (`Catcat/Layer1`)

| File | Contents |
|---|---|
| `Syntax.lean` | `Item`, the reader, printing |
| `Types.lean` | `Ty`, `Val`, `Name`, `Def`, `Env`, signature parsing |
| `Prim.lean` | the primitive table: fixed signatures and what each primitive computes |
| `Lower.lean` | lowering from syntax to kernel terms |
| `Run.lean` | decoding code values, the root model, `runSource` |

`Main.lean` is the command-line tool: `catcat FILE [FUEL]`.

### Lowering tracks the stack type

`lower` walks the items left to right carrying a `Shape`, the stack type so far. That is what lets it resolve an operation whose signature depends on the stack, such as `drop`, without a unifier.

The kernel's `infer` does not see a `Shape`. It computes a signature for the finished term from the labels alone. `runSource` checks that the two agree, so a mistake in lowering shows up as a disagreement, not as a wrong answer.

### Open shapes

A code block written without a signature is lowered from a `Shape` whose `inputs` field is `some []`. Popping a value the block has not pushed then records the expected type as an input, where a closed shape would report an underflow. The inputs collected by the end are the block's `pre`.

This only works for operations with a fixed signature. `drop` on an open, empty stack has no type to go by, so it is an error that asks for a signature.

### Termination of `lower`

`lower` recurses in two ways. Moving along a block shortens the item list. Entering a block or splicing a word's body does not, so those calls go through `depth`, which decreases. The measure is the pair `(depth, items.length)`.

A form such as `if { a } { b }` takes several items. The match on the head reports how many extra items it used, and the recursive call drops that many. Returning the remaining list directly would hide from Lean that it is shorter.

### Code values hold syntax

A `Val.code` holds the block's items, its signature and the `Env` it was written in. `Val.term?` lowers it again each time it is run.

It cannot hold a `Term` instead. A `Term` is built from operation names, a `Name` can be a literal `Val`, so a `Val` containing a `Term` would be defined in terms of itself across the kernel's type parameters. Holding syntax avoids that, and it is also the representation the language asks for: nothing can take the syntax back out.

For the same reason an `Env` holds each definition as syntax, and a recursive word seen from inside its own body is stored as a signature (`Def.label`), from which its operation label is rebuilt.

### Splicing

A word defined without a signature is lowered again at every call site. Two consequences:

- A definition that is never called is never checked.
- A word that calls another word twice doubles the term. Deep chains of such words grow exponentially. The emitter will share bodies; the interpreter does not.

### Defaults

`runSource` takes `fuel` (ten million) and `depth` (one thousand). Running out of either is an error, not a crash.
