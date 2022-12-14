ARCHIVED: see https://github.com/atennapel/tynka for a new implementation of this idea

Experimental implementation of a "dysfunctional" programming language.
The idea originates from this presentation by Andras Kovacs: https://www.youtube.com/watch?v=ai4vU1Naopk .

We have a language with two layers, one compile-time layer with full dependent types and a runtime-layer with a simply-typed language without higher-order functions or closures. We can get back higher-order functions and polymorphism in the compile-time layer, but after staging we get a very simple language that is easy to compile.

Try it out:
```
sbt "run examples/Test"
javac jvmstd/Pair.java
javac jvmstd/List.java
java Test
```

TODO:
- [x] Surface syntax
- [x] Parsing
- [x] Core syntax
- [x] Values
- [x] Evaluation
- [x] Unification
- [x] Globals
- [x] Elaboration
- [x] Pretty printing
- [x] Staging
- [x] IR syntax
- [x] Metas, zonking and unification
- [x] Meta insertion
- [x] Sigmas
  - [x] Syntax
  - [x] Parsing
  - [x] Elaboration
- [x] IR simplifier
- [x] IR lambda removal: eta expansion, closure conversion, lambda lifting
- [x] Bytecode generation
  - [x] Primitives
  - [x] Boxing/unboxing
  - [x] main method
  - [x] Definitions without parameters to static properties
- [x] Named sigma projection
- [x] Bool type with if expression
- [x] Allow if to return lambdas
- [x] Fixpoint
- [x] Add Int and primitive binops
- [x] Remove Nat
- [x] Tail recursion
- [x] Primitive polymorphic list datatype
  - [x] Type
  - [x] Constructors
  - [x] Elimination
- [ ] More simplification: case-of-case, app and case commutation
- [ ] Better inlining (inline linear lambdas, constants, globals)
- [ ] Combine jumps (for example if+comparisons)
