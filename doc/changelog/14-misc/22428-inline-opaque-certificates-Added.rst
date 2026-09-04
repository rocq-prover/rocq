- **Added:**
  ML API: ``Opaques.Summary.inline``, a variant of ``Opaques.Summary.join``
  that also replaces every computed certificate by the plain proof term it
  certifies, leaving an opaque table free of ``Future.computation``. The
  resulting table denotes the same proofs and, unlike a table of certificates,
  survives marshalling to another process
  (`#22428 <https://github.com/rocq-prover/rocq/pull/22428>`_,
  by remix7531).
