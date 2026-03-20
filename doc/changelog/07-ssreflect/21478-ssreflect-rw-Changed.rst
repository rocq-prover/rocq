- **Changed:**
  ``rewrite`` tactic for ``rw``. Since this was the major cause of
  conflict with legacy tactics, ssreflect can now be loaded with less
  conflicts through ``From Corelib Require Import ssreflect_rw.``.
  For backward compatibility
  ``From Corelib Require Import ssreflect.``
  still loads a ``rewrite`` wrapper to ``rw`` as well as the
  ``if <term> is <pattern> then <term> else <term>``
  and ``if <term> isn't <pattern> then <term> else <term>``
  syntactic sugars for match
  (`#21478 <https://github.com/rocq-prover/rocq/pull/21478>`_,
  by Pierre Roux).
