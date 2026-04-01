(* Reported in #12152 *)
Goal True.
Proof.
Fail intro H; auto.
Fail intros H; auto.
Abort.
