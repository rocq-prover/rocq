- **Added:**
  :cmd:`Definition` and similar commands support attributes
  :attr:`sealed` and :attr:`defined` to control :term:`opacity
  :<opaque>` without having to use an interactive proof.
  For instance `#[sealed] Definition foo := 0.` is equivalent to
  `Definition foo : nat. Proof. exact 0. Qed.` (except for inference of used section variables)
  (`#22713 <https://github.com/rocq-prover/rocq/pull/22713>`_,
  by Gaëtan Gilbert).
