- **Fixed:**
  ``rocqchk`` accepted proofs of ``False`` from crafted ``.vo`` files with
  forged primitive type registrations or primitive operator types. It also
  refused a library that uses a primitive literal after the module that
  registers its type
  (`#PRNUM <https://github.com/rocq-prover/rocq/pull/PRNUM>`_,
  by Sami Jawhar).
