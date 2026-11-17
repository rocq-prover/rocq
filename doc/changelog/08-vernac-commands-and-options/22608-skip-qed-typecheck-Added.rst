- **Added:**
  :flag:`Skip Qed Typecheck` flag, which skips the kernel typechecking of
  opaque proofs at :cmd:`Qed`; :cmd:`Print Assumptions` reports each such proof,
  and ``rocqchk`` still checks it in the libraries it checks
  (`#22608 <https://github.com/rocq-prover/rocq/pull/22608>`_,
  by Sami Jawhar, with help from Gaëtan Gilbert and Pierre-Marie Pédrot).
