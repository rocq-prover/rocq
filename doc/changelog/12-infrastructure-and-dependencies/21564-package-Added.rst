- **Added:**
  New notion of Rocq package and installation layout supported by a new
  command-line option ``-package DEP`` that automatically adds the correct
  ``-Q`` and ``-I`` options for ``DEP`` and its transitive dependencies.
  For backwards compatibility, the old installation scheme targeting the
  ``coq/user-contrib`` directory is kept, but the plan is to remove it
  after packages have been ported to the new installation scheme.
  The ``rocq makefile`` command can be made to rely on the new installation
  scheme by passing the ``--rocq-package PKGNAME`` argument, and optionally
  the ``--legacy-support`` argument to also install using the legacy
  installation scheme
  (`#21564 <https://github.com/rocq-prover/rocq/pull/21564>`_,
  by Rodolphe Lepigre).
