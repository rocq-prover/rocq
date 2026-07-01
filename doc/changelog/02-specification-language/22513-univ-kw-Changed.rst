- **Changed:**
  Introduced new keyword `Univ@{s;l}` to represent universes constructed from sort variables,
  rather than piggybacking on `Type@{s; _}` (where `s` could be `Type` itself).
  `Type` no longer elaborates to `Univ@{?s;?l}` except in template-polymorphic parameter
  declarations, where `s` will get instantiated to `Prop` or `Type`.
  Minor source of incompatibility: when :flag:`Collapse Sorts ToType` is `Unset`, `Type` now
  elaborates to `Type@{?l}` rather than generating a fresh sort
  (`#22513 <https://github.com/rocq-prover/rocq/pull/22513>`_,
  by Matthieu Sozeau).
