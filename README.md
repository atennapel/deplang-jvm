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
- [x] Sigmas
  - [x] Syntax
  - [x] Parsing
  - [x] Elaboration
- [ ] IR Lambda removal: eta expansion, closure conversion, lambda lifting
- [ ] Bytecode generation
- [ ] Named sigma projection
- [ ] Void, Unit, Bool types
- [ ] Datatypes
