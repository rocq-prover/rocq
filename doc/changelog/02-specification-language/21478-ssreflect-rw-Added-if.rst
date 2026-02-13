- **Added:**
  new syntactic sugar `if g is c then t else e`
  and `if g isn't c then t else e` for `match g with c => t | _ => e end`
  and `match g with c => e | _ => t end` respectively. This adds the
  new reserved keywords `is` and `isn't`
  (`#21478 <https://github.com/rocq-prover/rocq/pull/21478>`_,
  by Pierre Roux).
