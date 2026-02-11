- **Added:**
  :cmd:`Ltac2 Abbreviation` typecheck the body at declaration time instead of when they are used.
  This means incorrect abbreviations produce errors at declaration time, and also means quotations may be used inside abbreviations
  (e.g. `Ltac2 Abbreviation foo := @foo.`)
  (`#21617 <https://github.com/rocq-prover/rocq/pull/21617>`_,
  by Gaëtan Gilbert).
