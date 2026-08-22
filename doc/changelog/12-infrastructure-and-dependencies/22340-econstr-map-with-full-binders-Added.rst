- **Added:**
  ``EConstr.map_with_full_binders``, the map counterpart of
  ``EConstr.iter_with_full_binders``, which pushes the declarations bound by
  ``Case``, ``Fix`` and ``CoFix`` nodes as well as by ``Prod``, ``Lambda`` and
  ``LetIn``; ``Termops.map_constr_with_full_binders`` is now an alias for it
  (ML API change)
  (`#22340 <https://github.com/rocq-prover/rocq/pull/22340>`_,
  by Jason Gross).
