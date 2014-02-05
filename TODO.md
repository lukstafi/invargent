Place for TODOs/FIXMEs, especially if not expressed in other places. See README.md for broader-scope TODOs and source code for finer-scope TODOs and FIXMEs.

* TODO: perhaps `check_connected` could be simplified or even removed from abduction?
* FIXME: repeating `newtype` and `newcons` definitions should be errors.
* TODO: calibrate timeout parameters (number of iterations before forced exit from simple abduction, joint abduction etc.)
* FIXME: `separate_subst` has a default argument `keep_uni=false`. Rethink for each use case if it is the correct argument.
* TODO: more parsimonious use of parentheses in printing expressions and types.
* TODO: 'Update' and 'verify' modes of inference: use an existing `.gadti` file to provide a type annotation on the toplevel `.gadt` expressions. In update mode, if typechecking fails, retry without type annotation. In verify mode, check that the resulting type matches the interface type from `.gadti` -- is not less general. In update mode, regenerate the `.gadti` file.
* TODO: term abduction seems to no longer need alien premises. Rethink and remove.
* FIXME: missing `newtype` declarations should be errors. Do sort checking against declaration.
* TODO: introduce to the parser the syntax for `min` and `max` terms used by printing.
* FIXME: filtering / checking connected / simplification / initstep heuristic, for disjunction elimination, need rethinking and cleanup.
* TODO: remove postcondition atoms implied by the invariant.
* FIXME: check consistency of the order of `w` variables throughout `NumS`.
* FIXME: clean up the use of `localvs` for pruning and simplification.
* TODO: describe the behavior of `initstep` preserving facts about parameters in the documentation.