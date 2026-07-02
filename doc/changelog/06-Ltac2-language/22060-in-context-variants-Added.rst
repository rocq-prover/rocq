- **Added:**
  `Constr.Unsafe.in_context`, `Constr.in_context_prod`, and
  `Constr.in_context_letin` in Ltac2.
  `Constr.Unsafe.in_context` is a primitive that extends the proof
  context and returns a `binder * constr` pair.
  `Constr.in_context`, `Constr.in_context_prod`, and
  `Constr.in_context_letin` are wrappers that construct
  `Lambda`, `Prod`, and `LetIn` terms respectively
  (`#22060 <https://github.com/rocq-prover/rocq/pull/22060>`_,
  by Jason Gross).
