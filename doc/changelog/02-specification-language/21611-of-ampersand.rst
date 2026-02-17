- **Added:**
  new syntactic sugars `& T` for anonymous binders `(_ : T)`
  and `of T & ... & T` for anonymous binders in constructors, enabling the
  `Variant t := C1 of a & b & c | C2 x y of P x & Q y.` syntax.
  This adds the new reserved keyword `of`
  (`#21611 <https://github.com/rocq-prover/rocq/pull/21611>`_,
  by Pierre Roux).
