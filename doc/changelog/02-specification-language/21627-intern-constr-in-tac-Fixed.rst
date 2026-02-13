- **Fixed:**
  tactic definitions (:cmd:`Ltac`, :cmd:`Ltac2`, tactic notations, etc)
  correctly check that universe names are declared instead of delaying the error to when the tactic is used
  (`#21627 <https://github.com/rocq-prover/rocq/pull/21627>`_,
  fixes `#21616 <https://github.com/rocq-prover/rocq/issues/21616>`_,
  by Gaëtan Gilbert).
