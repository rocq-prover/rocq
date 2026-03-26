- **Fixed:**
  :cmd:`Print Assumptions` now also traverses the types of global
  definitions, not just their bodies, to detect dependencies on axioms
  that appear only in the type
  (`#21825 <https://github.com/rocq-prover/rocq/pull/21825>`_,
  by Jason Gross).
