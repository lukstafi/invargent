Place for TODOs/FIXMEs, especially if not expressed in other places. See README.md for broader-scope TODOs and source code for finer-scope TODOs and FIXMEs.

* TODO: factor out joint constraint abduction scheme, available for use across sorts (v2.0).
* TODO: numerical abduction -- optimize candidate substitution selection by working incrementally as in term abduction (FIXME: what did I mean?)
* TODO: optimize abduction, especially numerical, use iterative deepening or Best-First-Search
* FIXME: explain whether and why predicate variable solutions should be connected? And at what stage:: should connectedness be checked both pre- and post-filtering of chi candidate atoms in `split`? UPDATE: solved part of the question for binary predicate variables -- need connectedness to form the disjuncts.
* TODO: try using all branches for numerical abduction from the beginning, and only if this fails, starting without recursive branches.
* TODO: perhaps `check_connected` could be simplified or even removed from abduction?
* FIXME: repeating `newtype` and `newcons` definitions should be errors.
* TODO: I have removed connectedness checks. A variant of nested-definition related stuff might be needed when I get to mutual definition tests.
* TODO: breadth-first/iterative-deepening-like optimization for simple term abduction, where we do combinations of choices 1 and 6 before proceeding with other choices.
* TODO: optimize numerical abduction -- initial transformations should eliminate constants, universal variables, and rightmost remaining variables.
