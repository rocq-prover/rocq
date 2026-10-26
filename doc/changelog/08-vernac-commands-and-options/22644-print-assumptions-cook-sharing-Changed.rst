- **Changed:**
  :cmd:`Print Assumptions` keeps the sharing of an opaque proof while it
  expands the section's context, when it must discharge the proof over a
  section with an inductive type, so that step usually no longer costs time
  that grows with the size of the proof's tree unfolding
  (`#22644 <https://github.com/rocq-prover/rocq/pull/22644>`_,
  by Sami Jawhar).
