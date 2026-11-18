- **Changed:**
  the Proper normalization of setoid rewrite now cuts the search of some
  flipped instances, notably iff and eq. This makes the search much
  faster on some examples but there is a tiny risk of backwards
  incompatibility if the user declared Proper instances ending in (flip eq)
  or (flip iff), which should be virtually non-existent
  (`#22836 <https://github.com/rocq-prover/rocq/pull/22836>`_,
  by Pierre-Marie Pédrot).
