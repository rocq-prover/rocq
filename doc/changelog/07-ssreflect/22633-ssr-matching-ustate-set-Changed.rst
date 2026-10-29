- **Changed:**
  SSReflect pattern matching and rewriting no longer merge universe
  states for each matched occurrence, which makes ``rw`` and other
  tactics using patterns such as ``[X in T]`` or ``[e in X in T]``
  significantly faster on goals with many universe polymorphic
  occurrences. This also fixes a universe leak with patterns
  ``[e as X in T]`` where ``e`` has holes, which could make universes
  escape the proof (e.g. an unbound universe error with non-extensible
  universe binders)
  (`#22633 <https://github.com/rocq-prover/rocq/pull/22633>`_,
  by Matthieu Sozeau).
