- **Fixed:**
  the proof engine now keeps track of which hypotheses are section variables
  instead of assuming that a variable sharing a name with a section variable is a section variable.
  In particular :tacn:`destruct` now clears non-section-variable variables which share a name with a section variable.
  Note that modifying a section variable (e.g. with `apply in`) makes it a non-section-variable
  (`#21987 <https://github.com/rocq-prover/rocq/pull/21987>`_,
  fixes `#18858 <https://github.com/rocq-prover/rocq/issues/18858>`_
  and `#12304 <https://github.com/rocq-prover/rocq/issues/12304>`_
  and `#11487 <https://github.com/rocq-prover/rocq/issues/11487>`_
  and `#6773 <https://github.com/rocq-prover/rocq/issues/6773>`_,
  by Gaëtan Gilbert).
