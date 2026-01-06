- **Changed:**
  ``rewrite`` tactic for ``rw``. Since this was the major cause of
  conflict with legacy tactics, ssreflect can now be loaded in the
  Prelude. For backward compatibility ``From Corelib Require Import
  ssreflect.`` still loads a ``rewrite`` wrapper to ``rw``
  (`#21478 <https://github.com/rocq-prover/rocq/pull/21478>`_,
  by Pierre Roux).
