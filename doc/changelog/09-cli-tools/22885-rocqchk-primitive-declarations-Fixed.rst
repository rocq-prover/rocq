- **Fixed:**
  ``rocqchk`` accepted proofs of ``False`` from crafted ``.vo`` files with
  forged primitive type registrations or primitive operator types. It also
  refused a library that uses a primitive literal after the module that
  registers its type
  (`#22885 <https://github.com/rocq-prover/rocq/pull/22885>`_,
  by Sami Jawhar).
