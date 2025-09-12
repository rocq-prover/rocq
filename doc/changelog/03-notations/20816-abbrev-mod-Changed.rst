- **Changed:**
  :cmd:`Abbreviation` no longer adds a printing rule when a surrounding module is imported
  (i.e. when it would need to print a qualified name). :attr:`global` can be used
  to retrieve the previous behavior
  (`#20816 <https://github.com/rocq-prover/rocq/pull/20816>`_,
  fixes `#20668 <https://github.com/rocq-prover/rocq/issues/20668>`_,
  by Gaëtan Gilbert).
