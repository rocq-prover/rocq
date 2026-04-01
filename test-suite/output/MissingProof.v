Goal True.
  idtac.
  idtac. (* second command doesn't repeat the warning *)
Abort.

Goal True.
  {
Abort.

Goal True.
Admitted.

(* abort doesn't warn (NB it would be very annoying to make it warn
   because the stm sends the proof data from the proof opening command to Abort) *)
Goal True.
Abort.

Goal True.
Proof.
  Fail Proof.
Abort.

Goal True.
  idtac.
  Fail Proof.
Abort.
