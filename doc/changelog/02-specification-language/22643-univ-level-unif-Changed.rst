- **Changed:**
  universe levels generated during elaboration are now unification levels,
  printed `ℓi` like sort unification variables `αi`, instead of global levels
  named after the current module (e.g. `Foo:12`).
  They are numbered per command, so their names in messages and in the output
  of :flag:`Printing Universes` no longer depend on what was elaborated
  before. They are never declared in the kernel: monomorphic declarations
  replace the ones they keep by fresh global levels, and polymorphic
  declarations abstract them as before.
  Plugins that relied on fresh levels being global,
  e.g. to store them beyond the current command, must now substitute them
  (see `UState.globalize_levels`)
  (`#22643 <https://github.com/rocq-prover/rocq/pull/22643>`_,
  by Matthieu Sozeau).
