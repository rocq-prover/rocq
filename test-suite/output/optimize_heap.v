(* optimize_heap should not affect the proof state *)

Goal True.
Proof.
  idtac.
  Show.
  optimize_heap.
  Show.
Abort.
