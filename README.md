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
- [-] Normalize constraints.
- [_] Abduction for terms.
- [_] Abduction for linear systems.
- [_] Disjunction elimination for terms.
- [_] Disjunction elimination for linear systems.
- [_] Solve for predicate variables. Iterate till fixpoint.
- [_] Export (print) OCaml source. Optimize, perhaps write web interface.
- [_] Collect examples, test, write user documentation.
