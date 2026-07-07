- **Fixed:**
  Typeclass resolution failed eagerly when a goal had no applicable hint, without attempting the remaining goals, whose resolution may instantiate the failed goal's evars by unification; such goals are now deferred and retried after progress (regression in 9.3 from the goal-tactic association fix)
  (`#22228 <https://github.com/rocq-prover/rocq/pull/22228>`_,
  fixes `#22227 <https://github.com/rocq-prover/rocq/issues/22227>`_,
  by Jason Gross).
