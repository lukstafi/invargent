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

Milestones:
- [ ] Setup project. Parse and pretty-print.
- [ ] Generate constraints.
- [ ] Normalize constraints.
- [ ] Abduction for terms.
- [ ] Abduction for linear systems.
- [ ] Disjunction elimination for terms.
- [ ] Disjunction elimination for linear systems.
- [ ] Solve for predicate variables. Iterate till fixpoint.
- [ ] Export (print) OCaml source. Optimize, perhaps write web interface.
- [ ] Collect examples, test, write user documentation.
