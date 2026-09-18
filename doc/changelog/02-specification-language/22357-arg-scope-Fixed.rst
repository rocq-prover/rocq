- **Fixed:**
  ``f (x:=e)%s`` is now parsed as ``f (x:=e%s)`` instead of ``(f (x:=e))%s``
  (`#22357 <https://github.com/rocq-prover/rocq/pull/22357>`_,
  fixes `#22324 <https://github.com/rocq-prover/rocq/issues/22324>`_,
  by Gaëtan Gilbert).
