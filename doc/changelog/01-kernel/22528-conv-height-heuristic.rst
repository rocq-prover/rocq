- **Added:**
  New flag :flag:`Kernel Conversion Height Heuristic` that enables a conversion
  heuristic when comparing two constants.
  When enabled, a strategy level (see :cmd:`Strategy`) is
  set for each constant `c` upon definition. The set level is :g:`-h`,
  where :g:`h` is the `c`'s definitional height, which corresponds to
  the maximum number of constants that need to be unfolded in the
  definition of `c` to arrive at a term with no constants left to unfold.
  This heuristic over-approximates dependencies between constants by
  comparing their heights. Namely, if :g:`c1` depends on :g:`c2`, then
  :g:`||c1|| > ||c2||`. Thus, the set strategy levels will give
  priority to :g:`c1` over :g:`c2` during conversion.
  (`#22528 <https://github.com/rocq-prover/rocq/pull/22528>`_,
  by Gaspar Ricci).
