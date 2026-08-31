- **Added:**
  ML API: ``Opaques.Summary.inline``, a variant of ``Summary.join`` that also
  replaces every computed certificate by the plain proof term it certifies,
  leaving an opaque table free of ``Future.computation`` so embedders can
  marshal a ``Vernacstate.t`` that closed proofs. The table denotes the same
  value
  (`#22365 <https://github.com/rocq-prover/rocq/pull/22365>`_,
  by remix7531).
