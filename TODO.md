Place for TODOs/FIXMEs, especially if not expressed in other places. See README.md for broader-scope TODOs and source code for finer-scope TODOs and FIXMEs.

* FIXME: repeating `newtype` and `newcons` definitions should be errors.
* TODO: calibrate timeout parameters (number of iterations before forced exit from simple abduction, joint abduction etc.)
* TODO: more parsimonious use of parentheses in printing expressions and types.
* TODO: 'Update' and 'verify' modes of inference: use an existing `.gadti` file to provide a type annotation on the toplevel `.gadt` expressions. In update mode, if typechecking fails, retry without type annotation. In verify mode, check that the resulting type matches the interface type from `.gadti` -- is not less general. In update mode, regenerate the `.gadti` file.
* TODO: term abduction seems to no longer need alien premises. Rethink and remove.
* FIXME: missing `newtype` declarations should be errors. Do sort checking against declaration.
* FIXME: check consistency of the order of `w` variables throughout `NumS`.
* FIXME: optimize solved form of numerical inequalities by only storing GLB and LUB constants.
* FIXME: ater fallback, there is arity mismatch for parameters when computing verif_brs.
* TODO: fix problems with allowing min/max atoms with a constant as one of min/max arguments.
* FIXME: parsing of subtraction in types and expressions, e.g. "n - 1".