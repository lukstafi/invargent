Place for TODOs/FIXMEs, especially if not expressed in other places. See README.md for broader-scope TODOs and source code for finer-scope TODOs and FIXMEs.

* TODO: factor out joint constraint abduction scheme, available for use across sorts (v2.0).
* TODO: numerical abduction -- optimize candidate substitution selection by working incrementally as in term abduction (FIXME: what did I mean?)
* TODO: optimize abduction, especially numerical, use iterative deepening or Best-First-Search
* FIXME: explain whether and why predicate variable solutions should be connected? And at what stage:: should connectedness be checked both pre- and post-filtering of chi candidate atoms in `split`?
* FIXME: why without branch "simplification" the binary predicate variable lands in a separate branch?