# Roadmap

The work is in stages. Each stage lists what it delivers and what it depends on. Within a stage the items are in order.

## Stage 1: targets

Every target follows the pattern set by JavaScript: a model of a subset of the target language (syntax, printer, meaning), an emitter from kernel terms into that subset, and a three-way test (interpreter, model, real tool).

| | Item | Depends on |
|---|---|---|
| 1.1 | **JavaScript.** Done, except `compile` and deep recursion. | |
| 1.2 | **Fixed-width integers.** `i64` as a reinterpretation of `int`: agree with the unbounded model or fail a bounds check. WebAssembly and C have no native unbounded integer. | |
| 1.3 | **C.** A subset of C with a block-and-offset memory model, and an emitter. | 1.2, 2.1 |
| 1.4 | **WebAssembly.** A model of the instruction subset used, and an emitter. Lean formalizations of WebAssembly exist and may replace the hand-written model. | 1.2, 2.1 |
| 1.5 | **Tail calls and loops.** A recursive word whose call is in tail position becomes a loop, so depth is no longer bounded by the target's stack. | |

## Stage 2: memory

Syntax objects need a heap in C and WebAssembly, and later proofs of memory soundness need something precise to be about.

| | Item | Depends on |
|---|---|---|
| 2.1 | **The memory model.** Blocks with a size and a lifetime; an address is a block and an offset. Reads and writes outside a live block are errors in the model, never undefined. | |
| 2.2 | **Linear types in layer 1.** A value that may not be copied or dropped. The checker enforces it. | |
| 2.3 | **RAII primitives.** An owning handle to a block: create, read and write through it, release by an explicit destroying word. These are all that safe catcat code sees. | 2.1, 2.2 |
| 2.4 | **`Unsafe`.** Raw `alloc`, `free`, `load` and `store` are operations of an `Unsafe` effect. Code that performs them shows it in its free operations. | 2.1 |
| 2.5 | **The soundness statement.** A program whose free operations exclude `Unsafe` never reads or writes outside a live block and releases every block exactly once. Stated here, proved in stage 4. | 2.3, 2.4 |

## Stage 3: concurrency

| | Item | Depends on |
|---|---|---|
| 3.1 | **Tasks in the root model.** `spawn`, `yield` and channels as host operations. The root model holds several computations and steps them; no continuation is captured inside the language. | |
| 3.2 | **Demos.** Producer and consumer, a pipeline, a worker pool. Deterministic scheduling first, so they can be tested. | 3.1 |
| 3.3 | **Channels as linear values,** so a channel end cannot be used after it is closed. | 2.2, 3.1 |
| 3.4 | **Session types,** and the absence of deadlock as a typing property. | 3.3 |
| 3.5 | **Real threads** in a target. | 1.3 or 1.4, 3.1 |

## Stage 4: verification

The end goals are a catcat bootstrap interpreter proved to behave as the Lean reference does, and Lean integration proved to behave as a golden Lean implementation does. The steps toward them:

| | Item | Depends on |
|---|---|---|
| 4.1 | **The typed kernel.** Stacks indexed by their type, and the meaning function on them. Prove that `infer` is sound: a term it accepts never gets stuck, short of fuel. | |
| 4.2 | **The kernel laws K1–K4.** | 4.1 |
| 4.3 | **Lowering agrees with the kernel.** Today `prepare` checks this at run time for each program. Prove it once. | 4.1 |
| 4.4 | **Lean reachable from catcat.** An operation that hands a proposition to a Lean checker and branches on the answer. The checker is a trusted model, handled like any other. First by calling the Lean binary. | |
| 4.5 | **Terms as Lean definitions.** Print a kernel term as a Lean definition, so a statement about a catcat program is a Lean statement about that definition. | 4.4 |
| 4.6 | **Certified rewrites.** A rewrite carries a statement that it preserves meaning; 4.4 checks it. | 4.2, 4.5 |
| 4.7 | **Emitter correctness,** one target at a time: the model's run of the emitted program equals the kernel evaluator's run of the term. | 4.1, stage 1 |
| 4.8 | **Memory soundness** (2.5). | 4.1, stage 2 |
| 4.9 | **The interpreter in catcat.** Reader, lowering and evaluator written in catcat. Tested against the Lean reference on every program, then proved equivalent. Needs sum types and modules. | 4.5 |
| 4.10 | **A Lean checker in catcat.** A proof checker for exported Lean proofs, tested against the golden implementation, then proved equivalent. This replaces the binary of 4.4. | 4.9 |

## Designed, not built

- **Carriers.** A handler that changes what "the rest of the block" means, such as failure. A carrier is three words (`T`, `unit`, `bind`), and handling is a rewrite of the block that hands each sequel to `bind`. Needs sum types.
- **Layered syntax and macros.** Syntax objects in levels: level `n` lowers to level `n-1`, and level 0 lowers to code. A macro is a word run during one lowering step.
- **Schematic words.** A word that takes a syntax group at lowering time, by the same mechanism as a macro.
- **Code as an intermediate representation,** in place of raw syntax.
- **A general handler form in layer 1.** The kernel's `handle` is reachable today only through `let` and recursive `define`.

## Open questions

1. Parallel composition. The meaning function is sequential.
2. The relation under which a rewrite counts as meaning-preserving, and how invariants are carried through rewrites.
3. Clauses with several exits, so a handler can handle a branching operation.
4. Mutual recursion: one handler with several clauses.

## Later

- **Reader fusion.** A user-level reader that accepts `{5 +}` by inserting spaces, fused with the kernel reader, with a proof that the fused reader equals the composition of the two.
- Self-hosting: the implementation re-expressed in catcat and made faster through rewrites.
- Sealed types with invariants. Modules.
