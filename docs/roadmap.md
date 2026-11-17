# Roadmap

## Next

- **A JavaScript emitter.** The Lean evaluator is the semantics. The single trust assumption is that emitted code agrees with it, checked by differential testing. The first emitter is deliberately slow and Forth-like.
- **The kernel laws K1–K4,** and the typed-stack form of the meaning function that they are stated for.
- **A linear type,** so the type checker has something to enforce.

## Designed, not built

- **Carriers.** A handler that changes what "the rest of the block" means, such as failure. A carrier is three words (`T`, `unit`, `bind`), and handling is a rewrite of the block that hands each sequel to `bind`. On failure `bind` must consume whatever the block still holds, so a linear value held across a fallible operation is a type error. Needs sum types.
- **Layered syntax and macros.** Syntax objects in levels: level `n` lowers to level `n-1`, and level 0 lowers to code. Lowering proceeds outermost layer first. A macro is a word run during one lowering step.
- **Schematic words.** A word that takes a syntax group at lowering time, by the same mechanism as a macro.
- **Certified rewrites.** A function on syntax or terms that carries a proof that it preserves meaning under a stated relation. Reinterpretation, by contrast, is plain handling.
- **Fixed-width integers.** Treated as a reinterpretation of unbounded ones: agree with the unbounded model, or report a failed bounds check.
- **Code as an intermediate representation,** in place of raw syntax.
- **A general handler form in layer 1.** The kernel's `handle` is reachable today only through `let` and recursive `define`.

## Open questions

1. Parallel composition. The meaning function is sequential.
2. The relation under which a rewrite counts as meaning-preserving, and how invariants are carried through rewrites.
3. Clauses with several exits, so a handler can handle a branching operation.
4. Mutual recursion: one handler with several clauses.

## Later

- **Reader fusion.** A user-level reader that accepts `{5 +}` by inserting spaces, fused with the kernel reader, with a proof that the fused reader equals the composition of the two.
- WebAssembly, then a subset of C. Lean formalizations of WebAssembly exist, so the trust assumption could become a theorem there.
- Self-hosting: the implementation re-expressed in catcat and made faster through rewrites.
- Memory handlers, linear variables, sealed types with invariants.
- Concurrency with session types. Modules.
