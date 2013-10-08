Place for TODOs/FIXMEs, especially if not expressed in other places. See README.md for broader-scope TODOs and source code for finer-scope TODOs and FIXMEs.

* TODO: factor out joint constraint abduction scheme, available for use across sorts (v2.0).
* TODO: numerical abduction -- optimize candidate substitution selection by working incrementally as in term abduction (FIXME: what did I mean?)
* TODO: optimize abduction, especially numerical, use iterative deepening or Best-First-Search
* FIXME: explain whether and why predicate variable solutions should be connected? And at what stage:: should connectedness be checked both pre- and post-filtering of chi candidate atoms in `split`? UPDATE: solved part of the question for binary predicate variables -- need connectedness to form the disjuncts.
* TODO: try using all branches for numerical abduction from the beginning, and only if this fails, starting without recursive branches.
* TODO: try to find the maximally general type `equal1 : all a,b,c. (a,b)->c->c->Bool`. Currently, setting `Abduction.more_general := true` explodes the solver.
* FIXME: we are smuggling through a theoretical shortcoming in ESOP2014 paper regarding multi-parameter existential types. Sort it out both in implementation and in theory.