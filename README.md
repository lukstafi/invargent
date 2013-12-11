Invariant Generation as Type Inference with GADTs and Existentials.

Current project website: http://www.ii.uni.wroc.pl/~lukstafi/pmwiki/index.php?n=Infer.Infer

See documentation in the `doc` directory.

Makefile targets and installation:
```
make main   # build the executable
make docs   # build the documentation
make test   # build and perform the tests
make clean  # remove the executable and intermediate files
sudo cp ./invargent /usr/local/bin/invargent # optionally, install executable
```

Milestones: [x] - completed, [#] - finishing (75%-95%), [+] - in the middle (25%-75%), [-] - just started (5%-25%), [_] - not started.
- [x] Setup project. Parse and pretty-print.
- [x] Generate constraints.
- [x] Normalize constraints.
- [x] Abduction for terms. Multisort abduction part 1.
- [x] Abduction for linear systems. Multisort abduction part 2.
- [x] Multisort disjunction elimination (includes anti-unification).
- [x] Disjunction elimination for linear systems.
- [x] Solve for predicate variables related to recursive definitions. Iterate till fixpoint part 1.
- [x] Solve for predicate variables related to existential types. Iterate till fixpoint part 2.
- [x] Enforce convergence for numerical constraints. (Required for postconditions.)
- [x] Factorize joint constraint abduction scheme for use across sorts.
- [x] Add more tests and resolve issues that emerge.
- [x] Export (print) a file with inferred types, and OCaml source. Collect examples, write user documentation.

And version 2.0 goals:
- [_] Export to OCaml using built-in or pervasives OCaml types, in particular `bool` instead of `boolean`.
- [_] Ability to parse and import, i.e. "open", `.gadti` and `.mli` files. (v1.1)
- [_] Export Haskell code. (v1.1)
- [_] Factorize to make extending and adding sorts easier -- ideally, plug-in architecture for sorts. (v1.2)
- [_] Add (relational forms of) `min` and `max` to the numerical sort -- sorely needed for datastructure invariants. (v1.2)
- [_] Improve error reporting (likely culprit). (v1.3)
- [_] Optimize. (v1.3)
- [_] Syntax for numeric multiplication. (v2.0)
- [_] Add a new "promising" sort. Candidates: integer numbers, partial orders, ring of polynomials... (v2.0)
