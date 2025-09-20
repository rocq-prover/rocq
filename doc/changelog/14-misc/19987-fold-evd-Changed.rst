- **Changed:**
  The unification algorithm (evarconv) may need to unfold its two input terms to succeed. Now, when one of the terms is an evar, it instantiates it with the folded version of the other term. In other words, tactics now unfold less than before, which may change the behavior of subsequent tactics.
  (`#19987 <https://github.com/rocq-prover/rocq/pull/19987>`_,
  by Quentin Vermande).
