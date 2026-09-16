- **Fixed:**
  A :cmd:`Notation` that adds no parsing rule, such as an ``only printing``
  one, is no longer registered in the table of notation prefixes, which
  supplies default levels to the parsing rules of later notations sharing a
  prefix. An ``only printing`` ``_ == _`` with its right argument at
  level 16, declared before a parsing ``_ == _`` at level 70, used to make
  ``0 == 1 + 1`` parse as ``(0 == 1) + 1``
  (`#22480 <https://github.com/rocq-prover/rocq/pull/22480>`_,
  by remix7531).
