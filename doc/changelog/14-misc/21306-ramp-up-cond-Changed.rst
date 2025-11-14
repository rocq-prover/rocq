- **Changed:**
  use `Gc.ramp_up` while executing :cmd:`Require` on OCaml 5.4 and later.
  This should partially mitigate the performance lost since OCaml 4.14
  (`#21306 <https://github.com/rocq-prover/rocq/pull/21306>`_,
  by Gaëtan Gilbert).
