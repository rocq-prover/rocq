- **Changed:**
  Change computation of uniform-parameters for nested inductive types.
  Inductive types now need to be fully applied when nesting in order for
  parameters to be considered as uniform
  (`#21498 <https://github.com/rocq-prover/rocq/pull/21498>`_,
  fixes `#21497 <https://github.com/rocq-prover/rocq/issues/21497>`_,
  by Thomas Lamiaux).
