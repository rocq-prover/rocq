- **Fixed:**
  Batch compilation with :n:`-async-proofs on` now reports command and tactic
  errors instead of absorbing them, which could cause misleading later errors
  or incomplete ``.vo`` files
  (`#22423 <https://github.com/rocq-prover/rocq/pull/22423>`_,
  fixes `#19189 <https://github.com/rocq-prover/rocq/issues/19189>`_,
  by Jason Gross).
