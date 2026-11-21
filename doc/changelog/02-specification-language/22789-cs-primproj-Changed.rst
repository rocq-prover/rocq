- **Changed:**
  canonical structure inference, coercion classes, the unification of
  tactics and the SSReflect matcher treat all forms of a primitive
  projection alike: a canonical instance, a coercion or a pattern given
  with the projection, folded or unfolded, or with its compatibility
  constant is found for the other forms as well.
  For projections of structures which have canonical instances, the
  unification of tactics (used by :tacn:`apply`, :tacn:`rewrite` and
  typeclass resolution) no longer unfolds a record through a primitive
  projection before trying canonical structure inference, and it rejects
  a canonical solution which gives inconsistent values to the arguments
  of the instance instead of failing afterwards.
  This may change which unifier is found, or make more unification
  problems succeed, in developments which declare structures as
  primitive records
  (`#22789 <https://github.com/rocq-prover/rocq/pull/22789>`_,
  by Matthieu Sozeau).
