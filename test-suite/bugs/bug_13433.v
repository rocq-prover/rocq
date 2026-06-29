Goal True.
Proof.
  Fail let n := -1 in constructor n.
  (* todo timeout stills anomalies *)
  Fail let n := -1 in auto n.
Abort.
