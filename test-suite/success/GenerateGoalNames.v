(* -*- mode: coq; coq-prog-args: ("-generate-goal-names") -*- *)

Axiom A : forall (x : nat) P, x = x -> P.

(* eapply *)
Goal 0 = 0.
Proof.
  eapply A.
  [x]: exact 0.
  reflexivity.
Qed.

(* destruct *)
Goal forall A, A \/ A -> A.
Proof.
  intros A H.
  destruct H.
  [or_introl]: assumption.
  [or_intror]: assumption.
Qed.

(* induction *)
Goal forall x : list nat, x = x.
Proof.
  induction x.
  [nil]: reflexivity.
  [cons]: reflexivity.
Qed.
