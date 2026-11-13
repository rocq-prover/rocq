- **Fixed:**
  ``rocqchk`` accepted proofs of ``False`` from crafted ``.vo`` files with
  forged delta resolver aliases, primitive type registrations or primitive
  operator types. It also refused a library that uses a primitive literal
  after the module that registers its type
  (`#PRNUM <https://github.com/rocq-prover/rocq/pull/PRNUM>`_,
  fixes `#12439 <https://github.com/rocq-prover/rocq/issues/12439>`_
  and `#ISSUE <https://github.com/rocq-prover/rocq/issues/ISSUE>`_,
  by Sami Jawhar).
