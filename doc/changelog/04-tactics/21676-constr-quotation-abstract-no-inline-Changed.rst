- **Changed:**
  :tacn:`abstract`-ed subproofs within tactic quotations are not
  inlined any more. The previous behavior can be restored through
  the deprecated :flag:`Inline Abstract Subproof` flag
  (`#21676 <https://github.com/rocq-prover/rocq/pull/21676>`_,
  fixes `#7905 <https://github.com/rocq-prover/rocq/issues/7905>`_,
  by Pierre-Marie Pédrot).
