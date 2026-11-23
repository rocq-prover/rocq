- **Fixed:**
  ``rocqchk`` accepted proofs of ``False`` from crafted ``.vo`` files with
  forged delta resolver aliases, primitive type registrations or primitive
  operator types, or with a label used twice in a structure. It also
  refused a library that uses a primitive literal after the module that
  registers its type
  (`#22878 <https://github.com/rocq-prover/rocq/pull/22878>`_,
  fixes `#12439 <https://github.com/rocq-prover/rocq/issues/12439>`_
  and `#22877 <https://github.com/rocq-prover/rocq/issues/22877>`_,
  by Sami Jawhar).
