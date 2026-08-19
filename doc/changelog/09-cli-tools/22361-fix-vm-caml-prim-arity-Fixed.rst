- **Fixed:**
  ``rocqchk -bytecode-compiler yes`` no longer refuses to load files that use
  primitive strings; the VM data validator accepted only the six array
  primitives, so the bytecode of any string primitive failed to intern
  (`#22361 <https://github.com/rocq-prover/rocq/pull/22361>`_,
  fixes `#22360 <https://github.com/rocq-prover/rocq/issues/22360>`_,
  by Jason Gross).
