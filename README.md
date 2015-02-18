Invariant Generation as Type Inference with GADTs and Existentials.

Some additional information on the project: http://www.ii.uni.wroc.pl/~lukstafi/pmwiki/index.php?n=Infer.Infer

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

News: The order domain is postponed to v2.1. The v2.0 release is focused on improving completeness.

I decided to implement a new domain / sort. It will be an order domain, with bottom aka. zero element, top element, and successor. $p <= succ p, succ p <= p ==> p = top, p <= q && q <= p ==> p = q$. The subset of named elements (corresponding to the Herbrand model) is a linear order ($zero, succ zero, succ (succ zero), ..., top$), but the domain does not assume linearity. Thus it can be extended with incomparable constants in a future version.

Milestones: [x] - completed, [#] - finishing (75%-95%), [+] - in the middle (25%-75%), [-] - just started (5%-25%), [_] - not started.

Goals -- version targets may be reassigned:
- [-] New sort: order. (v2.1)
- [#] Order sort example: binomial heap. (v2.1)
- [ ] Datatype-level invariants shared by all constructors of a datatype. (v2.1)
- [ ] Solver directives in .gadt source code -- exposing the options available from the command-line interface. (v2.1)
- [ ] Or-patterns `p1 | p2` introducing disjunctions in premises, either eliminated by disjunction elimination or expanded by implication clause duplication -- depending on user-level option; preserved in exported code. (v2.1)
- [ ] Meta-automatic mode: retry with modified user-level parameter settings if inference fails. (v2.2)
- [ ] Improve error reporting (likely culprit). (v2.2)
- [ ] Ability to parse `.gadti` and `.mli` files, and use them with the module access `open M`, `let open M in ...`, `M.(...)` and `M.x` syntaxes. (v2.3)
- [ ] 'Update' and 'verify' modes of inference: use an existing `.gadti` file to provide a type annotation on the toplevel `.gadt` expressions. (v2.3)
- [ ] Optimize, paying attention to the speed of the update mode. (v2.3)
- [ ] Support OCaml-style records, with some desambiguation roughly as in OCaml. (v2.4)
- [ ] More general `when` clauses for patterns. Factorize `Num` and `NumAdd` out of the `expr` type. (v2.4)
- [ ] Add a new "promising" sort. Candidates: proper integer numbers, ring of polynomials... (v2.4)

Version 2.0 milestones are now completed:
- [x] Export to OCaml using built-in or pervasives OCaml types, in particular `bool` instead of `boolean`. (v1.1)
- [x] Support source code comments preserved in the AST. (v1.1)
- [x] Factorize to make extending and adding sorts easier. (v1.2)
- [x] Syntax for numeric multiplication by constant. (v1.2)
- [x] Add equations with a variable as LHS and `min` or `max` as RHS to the numerical sort. (v1.2)
- [x] `when` clauses for patterns, currently only for numerical inequalities. (v1.2)
- [x] Include negative numerical constraints (from `assert false`) as positive facts in numerical abduction, using disjunction elimination. (v1.2)
- [x] Add inequalities with a variable as one side and `min` as LHS or `max` as RHS to the numerical sort. (v1.2)
- [x] Flagship example: AVL tree from OCaml standard library (height imbalance limited by 2). (v1.2)
- [x] Option to detect all dead code. (v1.2.1)
- [x] Improve coverage for examples from Chuan-kai Lin's PhD thesis. (v2.0)
- [x] Improve coverage for DML / Liquid Types examples. (v2.0)
- [x] if-then-else syntax. (v2.0)

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
