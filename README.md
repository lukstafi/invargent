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

Milestones: [x] - completed, [#] - finishing, [+] - in the middle, [-] - just started, [_] - not started.
- [x] Setup project. Parse and pretty-print.
- [x] Generate constraints.
- [x] Normalize constraints.
- [x] Abduction for terms. Multisort abduction part 1.
- [-] Abduction for linear systems. Multisort abduction part 2.
- [_] Multisort disjunction elimination (includes anti-unification).
- [_] Disjunction elimination for linear systems.
- [_] Solve for predicate variables. Iterate till fixpoint.
- [_] Export (print) OCaml source. Optimize, perhaps write web interface.
- [_] Collect examples, test, write user documentation.

There are also post-release or near-release tasks:
- [_] Improve joint constraint abduction for terms.
- [_] Improve convergence-enforcing heuristics for numeric constraints.

And version 2.0 goals:
- [_] Factorize implementation to have plug-in architecture for sorts.
- [_] Add sorts: integer numbers,
- [_] finite partial orders,
- [_] atomless lattices,
- [_] ring of polynomials.
