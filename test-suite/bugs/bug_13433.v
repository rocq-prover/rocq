Goal True.
Proof.
  Fail let n := -1 in constructor n.
  Fail let n := -1 in auto n.
  Fail let n := -1 in timeout n idtac.
Abort.
