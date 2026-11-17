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
