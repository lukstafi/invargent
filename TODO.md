Place for TODOs/FIXMEs, especially if not expressed in other places. See README.md for broader-scope TODOs and source code for finer-scope TODOs and FIXMEs.

* FIXME: check each use of [unify ~use_quants:false], whether it shouldn't be [unify ~use_quants:true].
* TODO: treat params as first-to-eliminate variables in [unify] and make use of this feature.
* TODO: remove the use of parameters where [~use_quants:false] makes them obsolete.
* FIXME: does solving for existentials require abduction? Fix (remove?) quantifier handling for [abd_s].
* TODO: factor out joint constraint abduction scheme, available for use across sorts (v2.0).
* TODO: numerical abduction -- optimize candidate substitution selection by working incrementally as in term abduction
* FIXME: a separate fallback mechanism in the main loop for each sort
* TODO: optimize abduction, especially numerical, use Best-First-Search
