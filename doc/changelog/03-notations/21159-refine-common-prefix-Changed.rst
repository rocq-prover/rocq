- **Changed:**
  the ``notation-incompatible-prefix`` no longer warns about
  common prefixes followed by terminal symbols. For instance
  ``"x #0`` and ``"x #0 #1"`` are not incompatible since our
  parser isn't exactly LL1, considering successive terminal
  symbols as a single token. Note that this change has an
  impact on the default levels of such notations
  (`#21159 <https://github.com/rocq-prover/rocq/pull/21159>`_,
  by Pierre Roux).
