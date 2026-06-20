- **Added:**
  Little-endian number notation support via record wrapper types.
  New types ``Decimal.luint``/``lint``, ``Hexadecimal.luint``/``lint``,
  and ``Number.luint``/``lint`` can be used as target types for
  ``Number Notation``, causing the plugin to build digit lists with
  the least significant digit outermost
  (`#22135 <https://github.com/rocq-prover/rocq/pull/22135>`_,
  fixes `#22122 <https://github.com/rocq-prover/rocq/issues/22122>`_,
  by Jason Gross).
