- **Fixed:**
  loading module parameters with many substitutive objects no longer repeatedly
  rebuilds delta-resolver maps while composing substitutions.  Sequential
  compositions are recorded in a bounded persistent representation and
  normalized only after a bounded number of components, substantially reducing
  the time and memory needed for large module signatures
  (`#22303 <https://github.com/rocq-prover/rocq/pull/22303>`_,
  related to `#22279 <https://github.com/rocq-prover/rocq/issues/22279>`_,
  by Kanghee Park).
