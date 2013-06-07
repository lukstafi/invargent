Invariant Generation as Type Inference with GADTs and Existentials.

Current project website: http://www.ii.uni.wroc.pl/~lukstafi/pmwiki/index.php?n=Infer.Infer

See documentation in the `doc` directory.

Makefile targets:
```
make main   # build the executable
make docs   # build the documentation
make test   # build and perform the tests
make clean  # remove the executable and intermediate files
```

Milestones: [x] - completed, [#] - finishing (75%-95%), [+] - in the middle (25%-75%), [-] - just started (5%-25%), [_] - not started.
- [x] Setup project. Parse and pretty-print.
- [x] Generate constraints.
- [x] Normalize constraints.
- [x] Abduction for terms. Multisort abduction part 1.
- [#] Abduction for linear systems. Multisort abduction part 2.
- [x] Multisort disjunction elimination (includes anti-unification).
- [x] Disjunction elimination for linear systems.
- [-] Solve for predicate variables related to recursive definitions. Iterate till fixpoint part 1.
- [+] Solve for predicate variables related to existential types. Iterate till fixpoint part 2.
- [_] Write convergence-enforcing heuristics for numeric constraints.
- [_] Export (print) OCaml source. Collect examples, test, write user documentation.

And version 2.0 goals:
- [_] Formalize inference of GADT type definitions from function types.
- [_] Implement inference of GADT type definitions.
- [_] Optimize.
- [_] Write web interface.
- [_] Factorize implementation to have plug-in architecture for sorts.
- [_] Syntax for numeric multiplication.
- [_] Add sorts: integer numbers,
- [_] finite partial orders,
- [_] atomless lattices,
- [_] ring of polynomials.
