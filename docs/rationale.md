# Rationale

Why the kernel and the bootstrap language look the way they do. The definitions themselves are in [spec.md](spec.md).

## Aim

catcat sits between an intermediate representation and a high-level language. The long-term goals are manual JIT compilation as an ordinary language feature, a metacompiler that can bootstrap other syntaxes, and formal verification that survives rewriting. The method is to strip the core to the least that keeps full expressive power, and only then build it back up for performance.

The effect handler was chosen as the core because one construct then accounts for dynamic variables, recursion, interfaces, reinterpretation, mocking and effect tracking.

## The placement principle

A piece of code is given its meaning at the place it is used, so the handlers around that place apply to it.

The obvious alternative is to treat the dictionary of words as an outermost handler from names to bodies. It fails: a word's body is then emitted at the dictionary's position, outside every handler around the call. Bind a variable, call a word that reads it, and the read escapes the binding. Running a code value through an outermost handler fails the same way.

Three decisions follow.

- **Words are spliced.** Lowering replaces a word by its body at each call site. The dictionary is a lowering-time environment, not a runtime handler.
- **Recursion wraps the call site.** A recursive word cannot be spliced, so it becomes an operation handled by a `rec` handler placed around the call.
- **`run` unfolds in place.** A code value is decoded and given its meaning where the `run` is.

## Operations with several outcomes

Without code values on the stack, "pop a flag and run one of two blocks" cannot be an ordinary operation. The kernel also names no base type, so it has no value to inspect in an `if` form of its own.

So an operation may declare several result shapes, and the term supplies one branch per outcome. This is the usual shape of an algebraic operation whose result is a sum. The branches live in the operation's continuation, which keeps them inside the surrounding handlers. `if` is such an operation with two outcomes; taking a syntax object apart is one with four.

## Effect rows are computed

The row of a term is its set of free operations, computed the way free variables are. Nothing in a type mentions a row. This holds because code blocks written in place are part of the term, not values with a type of their own.

The exception is `run`: the operations of a code value are not known until it runs.

## Data is syntax

There is no memory effect and no list or array type. Unbounded data is the syntax object, as S-expressions are in Lisp. Its operations are pure functions on an immutable sequence, so there are no addresses and no aliasing to reason about.

The interface is a sequence (length, slice, concatenate), not a cons list. The list in the reference implementation is one model of it; arrays or ropes are others.

Mutable state comes from dynamic variables. Each variable is its own operation pair, so a term whose free operations do not include a variable provably cannot touch it. A variable alone is not a general store: only its innermost binding is visible, and bindings nest with the call stack, which makes it a pushdown structure.

## Code values

A code value is its syntax together with what is needed to lower it again. Nothing converts it back to a syntax object, so syntax can become code but code cannot become syntax. Later the representation can change to an intermediate form or a compact binary one without changing the language.

There is no currying. A value known when the block is written is embedded by writing it: `{ 5 + }`. A value known only at runtime reaches code through syntax and `compile`.

## Costs accepted

1. A word cannot be reinterpreted inside code that has already been lowered, because lowering replaced it by its body. Anything meant to be overridden later has to be an operation, or its syntax has to be lowered again.
2. A handler cannot handle an operation with several outcomes, so `if` and `view` cannot be reinterpreted in the language yet.
3. A stateful handler cannot be recursive.
4. The operations performed by `run` are not known statically.
5. There is no boolean type; tests give 1 or 0.
6. Every layer-1 value can be copied, so nothing yet exercises linearity.
