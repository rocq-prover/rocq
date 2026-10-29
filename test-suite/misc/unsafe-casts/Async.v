From UnsafeCasts Require Import Main.

(* The worker must load the plugin before independently checking this cast. *)
Lemma from_worker : rhs.
Proof. exact (lhs <:["test.vm-lhs"] rhs). Qed.
Print Assumptions from_worker.
