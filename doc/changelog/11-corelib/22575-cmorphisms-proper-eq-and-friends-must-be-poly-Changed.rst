- **Changed:**
  a few typeclass instances used internally by the setoid rewrite mechanism
  in Type were given a more general polymorphic universe quantification.
  This may cause subtle differences in universe unification for code using
  generalized rewriting in Type
  (`#22575 <https://github.com/rocq-prover/rocq/pull/22575>`_,
  by Pierre-Marie Pédrot).
