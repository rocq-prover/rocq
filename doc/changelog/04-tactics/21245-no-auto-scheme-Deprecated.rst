- **Deprecated:**
  dynamically generating schemes when needed in tactics.
  This was mostly used for rewriting and equality schemes of the registered equality type
  (`eq` when using the Corelib) for tactics such as :tacn:`discrimination`.
  These schemes are now explicitly declared for `eq` in the Corelib
  (`#21245 <https://github.com/rocq-prover/rocq/pull/21245>`_,
  by Gaëtan Gilbert).
