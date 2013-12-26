Invariant Generation as Type Inference with GADTs and Existentials.

Current project website: http://www.ii.uni.wroc.pl/~lukstafi/pmwiki/index.php?n=Infer.Infer

See documentation in the `doc` directory.

Makefile targets and installation:
```
make main   # build the executable
make docs   # build the documentation
make test   # build and perform the tests, with stacktraces
make testnative   # build and perform the tests, faster
sudo cp ./invargent /usr/local/bin/invargent # optionally, install executable
make clean  # remove the executable and intermediate files
```

Milestones: [x] - completed, [#] - finishing (75%-95%), [+] - in the middle (25%-75%), [-] - just started (5%-25%), [_] - not started.

Version 2.0 goals -- version targets may be reassigned:
- [x] Export to OCaml using built-in or pervasives OCaml types, in particular `bool` instead of `boolean`. (v1.1)
- [x] Support source code comments preserved in the AST. (v1.1)
- [#] Factorize to make extending and adding sorts easier. (v1.2)
- [+] Syntax for numeric multiplication. (v1.2)
- [-] Add (relational forms of) `min` and `max` to the numerical sort -- sorely needed for datastructure invariants. (v1.2)
- [_] Ability to parse `.gadti` and `.mli` files, and use them with the module access `open M`, `let open M in ...`, `M.(...)` and `M.x` syntaxes. (v1.3)
- [_] Export Haskell code. (v1.3)
- [_] Meta-automatic mode: retry with modified user-level parameter settings if inference fails. (v1.3)
- [_] Improve error reporting (likely culprit). (v1.4)
- [_] 'Update' and 'verify' modes of inference: use an existing `.gadti` file to provide a type annotation on the toplevel `.gadt` expressions. (v1.4)
- [_] Optimize, paying attention to the speed of the update mode. (v1.4)
- [_] Support OCaml-style records, with some desambiguation roughly as in OCaml. (v1.4)
- [_] Or-patterns `p1 | p2` expanded for inference but preserved in exported code. (v1.4)
- [_] Add a new "promising" sort. Candidates: integer numbers, partial orders, ring of polynomials... (v2.0)

Version 1.0 milestones are now completed:
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
