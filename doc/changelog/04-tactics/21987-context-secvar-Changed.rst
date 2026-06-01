- **Changed:**
  :tacn:`clear` checks that identifiers are bound even when they are ltac variables
  (typically in `match goal with H : _ |- _ => foo H; clear H end`, `clear` now fails if `foo` cleared H where before it would succeed without doing anything)
  (`#21987 <https://github.com/rocq-prover/rocq/pull/21987>`_,
  by Gaëtan Gilbert).
