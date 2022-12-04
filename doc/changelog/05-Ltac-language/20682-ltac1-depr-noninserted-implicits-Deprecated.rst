- **Deprecated:**
  interpreting a :n:`@qualid` argument to a ltac as a term (with insertion of any implicit arguments, unfolding notations, etc)
  in a toplevel :cmd:`Ltac` definition instead of interpreting it as the reference without implicit arguments.
  Enable flag :flag:`Ltac Always Insert Implicits` to get the future behaviour.
  Note that tactics in proof scripts already interpret :n:`@qualid` arguments as terms, so enabling the flag unifies the two behaviours
  (`#20682 <https://github.com/rocq-prover/rocq/pull/20682>`_,
  by Hugo Herbelin and Gaëtan Gilbert).
