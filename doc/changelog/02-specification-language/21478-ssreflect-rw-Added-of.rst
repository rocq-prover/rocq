- **Added:**
  new syntactic sugars `of T` and `& T` for anonymous binders
  `(_ : T)`. In particular, this enables the
  `Variant t := C1 of a & b & c | C2 of d.` syntax.
  This adds the new reserved keyword `of`
  (`#21478 <https://github.com/rocq-prover/rocq/pull/21478>`_,
  by Pierre Roux).
