- **Fixed:**
  A :cmd:`Notation` that adds no parsing rule, such as an ``only printing``
  one, is no longer registered in the table of notation prefixes. That table
  gives default levels to, and checks the factorization of, the parsing rules
  of later notations sharing a prefix, so a declaration with no parsing rule of
  its own used to leak its argument levels into them: an ``only printing``
  ``_ == _`` with its right argument at level 16, declared before a parsing
  ``_ == _`` at level 70, made ``0 == 1 + 1`` parse as ``(0 == 1) + 1``
  (`#22480 <https://github.com/rocq-prover/rocq/pull/22480>`_,
  by remix7531).
