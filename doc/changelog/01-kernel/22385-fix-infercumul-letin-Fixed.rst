- **Fixed:**
  incorrect variance inference for :ref:`cumulative inductives <cumulative>`
  with letins in the constructor type (bodies of constructor letins can be extracted by `match` without appearing in the `match` term, so they must be considered invariant positions instead of irrelevant)
  (`#22385 <https://github.com/rocq-prover/rocq/pull/22385>`_,
  fixes `#22383 <https://github.com/rocq-prover/rocq/issues/22383>`_,
  by Gaëtan Gilbert).
