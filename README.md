# catcat

A statically stack-typed concatenative language built on one construct, the effect handler. The name is con**cat**enative plus **cat**egorical.

The kernel has four structural term forms and `run`. Dynamic variables, recursion, late binding, reinterpretation and effect tracking all come from its single handler construct; word definitions need no kernel support at all. A small bootstrap language is defined on top by translation to kernel terms. Both layers are written in Lean 4, and the Lean sources are the reference.

```
define fact ( int -- int ) {
  pick [ 0 ] if { pick [ 0 ] 1 - fact * } { drop 1 }
}

30 fact
```

## Status

Early. The kernel, the bootstrap language, an interpreter and a JavaScript emitter work. Nothing is proved yet. See [docs/roadmap.md](docs/roadmap.md).

## Building

With Nix:

```
nix develop
lake build
```

Without Nix, install [elan](https://github.com/leanprover/elan); `lean-toolchain` selects the compiler. There are no other dependencies.

```
lake exe catcat examples/factorial.cat       # run a program
lake exe catcat js examples/factorial.cat    # print it as JavaScript
lake test                                    # run every example and test
```

A program prints whatever it emitted, then its final stack, bottom first. An optional second argument sets the fuel, which bounds recursion: `lake exe catcat FILE 100000000`.

`lake test` runs each program three ways and compares them: the interpreter, a Lean model of the JavaScript subset running the emitted program, and `node` running its printed text (skipped when `node` is not installed).

## Layout

| Path | Contents |
|---|---|
| `Catcat/Kernel/` | layer 0: terms, typing, evaluation |
| `Catcat/Layer1/` | layer 1: reader, lowering, primitives, interpreter |
| `Catcat/JS/` | a model of a JavaScript subset, and the emitter that targets it |
| `Main.lean`, `Test.lean` | the command-line tool and the test runner |
| `examples/` | programs, each with its expected output |
| `tests/` | small cases for single behaviours and errors |
| `docs/spec.md` | the specification of both layers |
| `docs/rationale.md` | why they are shaped this way |
| `docs/implementation.md` | notes on the Lean sources |
| `docs/roadmap.md` | what is next and what is open |

## Examples

| File | Shows |
|---|---|
| `factorial.cat` | recursion |
| `variables.cat` | dynamic variables and shadowing |
| `sequences.cat` | syntax objects as data: sum, reverse, map |
| `hello.cat` | output |
| `fizzbuzz.cat` | the above together |
| `calculator.cat` | an interpreter for a postfix language, written in catcat |
| `specialize.cat` | code built and compiled at run time |
