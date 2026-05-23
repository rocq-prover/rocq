- **Added:**
  `Constr.map_with_full_binders` and `Constr.Unsafe.map_with_full_binders` in Ltac2,
  which map a function on the immediate subterms of a constr, using
  `Unsafe.in_context` to traverse under binders so that the mapped
  function operates on well-typed terms in proper contexts
  (`#22062 <https://github.com/rocq-prover/rocq/pull/22062>`_,
  by Jason Gross).
