- **Fixed:**
  incorrect variance inference for :ref:`cumulative inductives <cumulative>`
  with applied stuck matches from irrelevant to relevant types
  (eg match from `sFalse : SProp` or identity in SProp (the later needing :flag:`Definitional UIP`)
  to a relevant type)
  (`#22377 <https://github.com/rocq-prover/rocq/pull/22377>`_,
  fixes `#22376 <https://github.com/rocq-prover/rocq/issues/22376>`_,
  by Gaëtan Gilbert).
