# catcat initial draft, version 1

The ideal goal is a language which accomplishes all of the following at once:

- Fast manual JIT compilation
  - Manual JIT, integrated into the syntax and type system, for speed is a primary goal
- Runtime speed which trades blows with C/Rust, especially when the ahead-of-time portions are compiled by LLVM
- Expressive semantics with Haskell-inspired purity and category theory in the type/effect system
- A Forth-inspired concatenative language model with simple syntax, stack semantics, and natural linear typing
- The ability to use macros, parser tooling, and/or compiler overrides to bootstrap into a compiler for another language
  - One vision is to transpile to this simple language as a host for both ahead-of-time and JIT compilation
  - This mitigates potential issues with the language being concatenative. If it doesn't sell, wrap it with something more Rust-like.
  - If this language is semantically rich and syntactically basic, then I see this as the best tradeoff for a metacompiler: subtractive semantic modeling, additive syntactic refinement.
- Excellent interactive tooling, including:
  - The ability to use the language as a scripting language
  - An extremely fast language server which uses lessons from tree-sitter and the language's optimized type system to update inferred types in real time
  - Serious debugging, profiling, and tracing tools which allow reinterpretation of the whole program to assist analysis upon failure
- A proof-oriented core, developed in F*.
  - Potential for integrating dependent typing into the core, but this is lowest-priority.

Accomplishing all of this is nigh unthinkable prior to the recent advances of AI. But now, it might be possible to take this type of idea seriously. Even if some of these ideas end up not panning out, I can give up on some of the above. However, manual JIT and metacompiler functionality are critical goals of this project.

The development plan is to assemble a mechanized spec in F*, then put together a working interpreter for proof-of-concept, then get a working compiler, all of which provably match the spec's semantics. Then each optimization pass must provably match the behavior of the original code, according to spec rules which consider the full application as an unstructured DAG of computations by default. Cranelift will be useful for the initial compiler, but eventually making the whole core of the compiler proof-oriented is ideal, and assumptions like aliasing cannot be exploited by Cranelift from what I've heard.

The Forth-like language was chosen partially because I wanted to see how far concatenative could be taken, but mainly for practical reasons: the simpler the language, the easier it is to set up, and the easier macros are to work with. Lisp was another option, but traditional list-based Lisp is not ideal for this project, and Lisp tends to not mesh well with heavy typing or totally GC-free setups. Forth was designed for bare metal, and word-oriented programming with functions composing in order has serious advantages which are underutilized to this day. I don't plan on having a return stack, there will be heavy compilation, and the type system will be very strict (though probably with heavy type inference), so it diverges substantially from the original Forth in goals and mechanics. The IMMEDIATE system is interesting for its ability to poke into the compiler and consume words which come afterward, but this probably needs to be constrained for simpler parsing. And variadic functions will not exist: stacks will be statically typed on inputs and outputs.

The type system is aimed at being as minimal as possible while enabling rich features. The current plan has the following structure:

- Primitive types similar to C/Rust
- Function composition which is simple and fast to compute, almost like currying but without curried functions as first-class in the type system
  - With stack head on left, a function [int int] -> [float] followed by [float int] -> [str str] composes trivially into [int int int] -> [str str]
- First-class functions may not exist, unlike many functional languages, especially with the JIT system
- Product/sum types may similarly not be primitive
- Type access erasure will naturally allow OOP/encapsulation: bundle up 1 or more stack values and treat them as 1 conjoined value, where class methods are the only ones allowed to touch the values directly
  - This removes the need for a separate struct/tuple/product type in the type system
- A rich effect system to tie everything together
  - Function-level free monads. Every effect is reentrant because non-reentrant effects didn't seem to have a good setup with the stack model
  - To call a function which has an effect, the parent function must either propagate the effect or provide a handler for the effect
  - Certain effects are built-in to the compiler, particularly side-effects including IO and concurrency primitives
  - Importantly, built-in effects include dynamically-scoped variable behavior and especially the Dictionary itself!
    - The latter makes reinterpretation of programs under different rules natural.
  - Macros will themselves have effects annotating their impact on the lexer/parser/compiler pipeline.
    - Just like how stack effects are not variadic, macros should also probably not be variadic, and should rather have an effect annotation to immediately consume N words to the right.
  - Effects integrate with the aforementioned OOP, as they can be used to declare the interface of the class, as discussed below.
  - Last but not least, effects provide a nice mechanism for JIT: a runtime JIT function is just a function which has user-defined effects instantiated at runtime.

The Haskell/category theory-inspired parts are:

- Effects enabling true purity
- Effects behaving as *free monads*
- The ability to quickly analyze a function purely from its signature of stack types and effects, and treat it as a black box for composition
- The ability to treat a program as a complete composition of functions, without reference to data, Yoneda embedding-style
- Derived types which act as functors for easy reinterpretation of programs
  - If we have a function which operates on float and computes the hypotenuse, we could simply transform that function to one which operates on a SIMD[float], or an array of float, or an array of SIMD[float].
  - This transformation might be performable automatically, as though with implicit casts: if the inputs are SIMD[float] instead of float
    - If it conflicts with speed, forget automatic deduction here.
  - Remember that the Dictionary effect will enable overriding words down to the primitive level, and functors can sit atop this layer
- Potential for monadic types, as monads are just extended functors

Here's a sketch of a Counter class built on top of an int:

```
define-effect __Interface_Counter[T]
interface {
  declare-word new ( -- T ) ;
  declare-word delete ( T -- ) ;
  declare-word create ( -- T ) ;
  declare-word increment ( T -- T ) ;
  declare-word getCount ( T -- T int ) ;
} ;

instantiate-class Counter int (__Interface_Counter)
{
  define-word new  0 ;
  define-word delete  pop ;
  define-word create  new ;
  define-word increment  1+ ;
  define-word getCount  dup ;
}
```

I still haven't formalized anything, so there are rough edges. The things which I think are settled are:

- {} corresponds to blocks of code. It will be possible for an effect handler or IMMEDIATE-like macro to consume a single {} block as though it's an anonymous word, then possibly reinterpret it under different rules (like the SIMD functor case above).
- () corresponds not to comments, but to type annotations as in Forth.
  - To make it more general, () corresponds to any block which doesn't use the default lexer/parser, so lexing/parsing can be deferred.
- [] corresponds to generics in typing.

These can form most of the syntax, with much of the syntax being formed via macros. Unlike Forth, I want to keep syntax minimal but not totally free-form, as this hurts tooling like LSPs.
