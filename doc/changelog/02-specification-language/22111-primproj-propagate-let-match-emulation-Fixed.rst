- **Fixed:**
  pattern-matching emulation for primitive records now types
  the branch in a context where the constructor variables are
  let-bound to the projection of the scrutinee, restoring the
  completeness of the typing rule
  (`#22111 <https://github.com/rocq-prover/rocq/pull/22111>`_,
  fixes `#22110 <https://github.com/rocq-prover/rocq/issues/22110>`_,
  by Pierre-Marie Pédrot).
