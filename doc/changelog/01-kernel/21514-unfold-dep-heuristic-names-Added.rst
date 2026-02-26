- **Added:**
  new flag :flag:`Kernel Conversion Dep Heuristic` that enables a heuristic for
  smarter constant unfolding during conversion. When enabled, if two constants
  have the same strategy level (see :cmd:`Strategy`) and one constant's
  definition depends on the other, the dependent constant is unfolded first.
  This can significantly speed up conversions in cases like checking ``c1 =
  c2`` vs ``c2 = c1`` where one definition wraps the other. The flag defaults
  to off, preserving the existing behavior of preferentially unfolding the
  right-hand side first (`#21514
  <https://github.com/rocq-prover/rocq/pull/21514>`_, fixes `#21509
  <https://github.com/rocq-prover/rocq/issues/21509>`_, by Jason Gross).
