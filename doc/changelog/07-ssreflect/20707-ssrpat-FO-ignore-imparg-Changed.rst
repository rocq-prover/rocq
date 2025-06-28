- **Changed:**
  rewrite pattern selection algorithm made more robust in face of changes
  to implicit arguments shape. This changes can result in a different
  pattern selection in some corner cases.
  The option `Set SsrMatching LegacyFoUnif` can be used to obtain the
  previous behavior when repairing scripts
  (`#20707 <https://github.com/rocq-prover/rocq/pull/20707>`_,
  fixes `#16763 <https://github.com/rocq-prover/rocq/issues/16763>`_,
  by Enrico Tassi with help from Georges Gonthier, Pierre Roux and
  Quentin Vermande).
