Fail Fixpoint F (n : nat) : nat :=
  match n with
  | O => O
  | S k =>
    (fix f (p : nat) (m : nat) {struct m} :=
       match m with O => p | S m' => g (S p) m' end
     with g (q : nat) (m : nat) {struct m} :=
       match m with O => F q | S m' => f q m' end
     for f) k k
  end.

(*
Lemma F_S k:
  F (S k) =
    (fix f (p : nat) (m : nat) {struct m} :=
       match m with O => p | S m' => g (S p) m' end
     with g (q : nat) (m : nat) {struct m} :=
       match m with O => S (F q) | S m' => f q m' end
     for f) k k.
Proof.
  reflexivity.
Qed.

Lemma F_S':
  F 2 = S (F 2).
Proof.
  etransitivity.
  1: rewrite F_S.
  all: reflexivity.
Qed.

Goal False.
Proof.
  pose proof F_S'.
  remember (F 2).
  clear Heqn.
  induction n.
  - congruence.
  - inversion H; subst; tauto.
Qed.
*)
