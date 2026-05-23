- **Fixed:**
  ``EConstr.contract_case`` no longer anomalies on case branches
  containing solved evars. The function now normalizes evars in
  branches and the return predicate before passing them to the kernel
  (`#22058 <https://github.com/rocq-prover/rocq/pull/22058>`_,
  fixes `#22058 <https://github.com/rocq-prover/rocq/issues/22058>`_,
  by Jason Gross).
