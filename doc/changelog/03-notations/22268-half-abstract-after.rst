- **Added:**
  :cmd:`Number Notation` option ``half abstract after n via f2 f1``:
  above the threshold ``n``, literals are parsed to the unreduced
  application of ``f2`` to the normal form of ``f1`` applied to the raw
  literal, a targeted middle ground between full reduction and
  ``abstract after``
  (`#22268 <https://github.com/rocq-prover/rocq/pull/22268>`_,
  by Jason Gross).
- **Changed:**
  large :g:`nat` literals (above 5000) are parsed to
  :g:`Nat.of_num_little_uint` applied to little-endian digits instead of
  an unreduced application of :g:`Nat.of_num_uint`
  (`#22268 <https://github.com/rocq-prover/rocq/pull/22268>`_,
  by Jason Gross).
