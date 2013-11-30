Place for TODOs/FIXMEs, especially if not expressed in other places. See README.md for broader-scope TODOs and source code for finer-scope TODOs and FIXMEs.

* TODO: factor out joint constraint abduction scheme, available for use across sorts (v2.0).
* TODO: numerical abduction -- optimize candidate substitution selection by working incrementally as in term abduction (FIXME: what did I mean?)
* TODO: optimize abduction, especially numerical, use iterative deepening or Best-First-Search
* TODO: try using all branches for numerical abduction from the beginning, and only if this fails, starting without recursive branches.
* TODO: perhaps `check_connected` could be simplified or even removed from abduction?
* FIXME: repeating `newtype` and `newcons` definitions should be errors.
* FIXME: in `split`, instead of undirected connectedness `ans4`, filter atoms whose free variables have at most a single variable more than the corresponding `ans3`, and it is existential.
* TODO: Emacs does not hyperlink error communicates -- change error format?
