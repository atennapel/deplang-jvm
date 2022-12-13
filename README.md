Experimental implementation of a "dysfunctional programming".
The idea originates from this presentation by Andras Kovacs: https://www.youtube.com/watch?v=ai4vU1Naopk .

Try it out:
```
sbt "run examples/Test"
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
- [ ] Sigmas
  - [x] Syntax
  - [ ] Parsing
  - [ ] Elaboration
  - [ ] Remove PairTy
  - [ ] Named projection
- [ ] IR Lambda removal: eta expansion, closure conversion, lambda lifting
- [ ] Bytecode generation
