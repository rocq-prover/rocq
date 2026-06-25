- **Fixed:**
  when a sort variables is constrained with `Prop <= q` but does not require `q <= Type`,
  it will be collapsed to `Prop` instead of `Type`
  (`#22170 <https://github.com/rocq-prover/rocq/pull/22170>`_,
  fixes `#22152 <https://github.com/rocq-prover/rocq/issues/22152>`_,
  by Gaëtan Gilbert).
