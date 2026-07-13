- **Fixed:**
  notations for `Number.uint` and `Number.int` that were broken
  since the introduction of hexadecimal variants.
  The notations are now accessible in the `%uint` and `%int`
  scopes, binded in functions like `Nat.of_num_uint`
  (`#22270 <https://github.com/rocq-prover/rocq/pull/22270>`_,
  by Pierre Roux).
