- **Changed:**
  :cmd:`Print Assumptions` and ``rocqchk`` keep the sharing of an opaque proof
  while they expand the section's context in it, when they discharge it over a
  section, so that step usually no longer costs time that grows with the size
  of the proof's tree unfolding
  (`#22644 <https://github.com/rocq-prover/rocq/pull/22644>`_,
  by Sami Jawhar).
