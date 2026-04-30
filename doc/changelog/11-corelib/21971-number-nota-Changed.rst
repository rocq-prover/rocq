- **Changed:**
  number notations for `nat` `Number.int` and `Number.uint` are now declared in `NumberNotations` submodules of `Nat` and `Number`. The submodules are exported from `Nat` and `Number` (which are not imported by default) and from `Prelude` (which is imported by default) so visible changes should be rare
  (`#21971 <https://github.com/rocq-prover/rocq/pull/21971>`_,
  by Gaëtan Gilbert).
