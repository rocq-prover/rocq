- **Changed:**
  hints from a functor argument whose underlying reference is
  marked Inline in the functor parameter type are not expanded
  into their inlined value anymore at application time. This
  prevents arbitrary terms from flowing into hint databases.
  This change is not backwards compatible but breakage should
  be extremely uncommon
  (`#21862 <https://github.com/rocq-prover/rocq/pull/21862>`_,
  by Pierre-Marie Pédrot).
