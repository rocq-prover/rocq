- **Added:**
  in :ref:`sort polymorphic <sort-polymorphism>` instances, sorts can be separated from universes using `;` instead of `|`.
  This is less ambiguous as `|` is also used to separate universes and constraints when declaring sort polymorphic objects,
  and in such declarations when constraints are unspecified it allows omitting the `|`
  (`Definition foo@{s;u} := ...` instead of `Definition foo@{s|u|+} := ...`)
  (`#20635 <https://github.com/rocq-prover/rocq/pull/20635>`_,
  by Gaëtan Gilbert).
