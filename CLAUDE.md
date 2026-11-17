# catcat

A concatenative language on an effect-handler kernel, specified and implemented in Lean 4.

## Read first

1. `docs/spec.md`: the kernel (layer 0) and the bootstrap language (layer 1). The Lean sources are the reference.
2. `docs/rationale.md`: the reasons, chiefly the placement principle.
3. `docs/implementation.md`: how the sources realize the spec.
4. `docs/roadmap.md`: what is next and what is open.

## Commands

```
nix develop                              # provides elan; lean-toolchain pins the compiler
lake build
lake test                                # every program in examples/ and tests/
lake exe catcat examples/factorial.cat
```

`lake build` and `lake test` must pass before a commit.

## Conventions

- **Stack order.** Every list of types or values is top-first. Source signatures are written bottom to top.
- **Short code.** Keep code short and focused, spec code above all. An explanation that needs room goes in `docs/implementation.md`, not in a comment.
- **Comments** give a reason or a non-obvious invariant. Never restate the code.
- **Totality.** No `partial` and no `sorry` in `Catcat/`. A call that is not structural takes fuel.
- **Tests.** A new behaviour gets a `.cat` file in `tests/` with its `.expected` output. Read the output before recording it.
- **NixOS.** The dev shell must keep working there; do not add tools that need a global install.
