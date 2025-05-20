- **Added:**
  antiquotation `$hyp:id` in terms for dynamically named hypotheses,
  i.e. `let x := @y in constr:($hyp:x)` is equivalent to `constr:(&y)`
  (`#20656 <https://github.com/rocq-prover/rocq/pull/20656>`_,
  by Gaëtan Gilbert).
