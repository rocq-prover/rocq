- **Fixed:**
  Typeclass resolution failed eagerly when a goal had no applicable hint,
  even when resolving the remaining goals would have instantiated the failed
  goal's evar by unification; failed final resolutions are now retried once
  with such goals ordered last (regression in 9.3 from the goal-tactic
  association fix)
  (`#22228 <https://github.com/rocq-prover/rocq/pull/22228>`_,
  fixes `#22227 <https://github.com/rocq-prover/rocq/issues/22227>`_,
  by Jason Gross).
