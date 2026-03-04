Section A. Variable (F_let : nat -> nat).
Fixpoint f (p : nat) (m : nat) {struct m} :=
 match m with
 | O => S p
 | S m' =>
   let h := g in
   h (S p) m'
 end
with g (q : nat) (m : nat) {struct m} :=
 match m with
 | O => S (F_let q)
 | S m' => f q m'
 end.
End A.

Fail Fixpoint F_let (n : nat) : nat :=
  let r :=
  match n with
  | O => O
  | S k =>
    f F_let k n
  end in r.

(*
Theorem false n : n = F_let 1 -> match F_let 1 with 0 => False | S n' => n = n' end.
  intro e.
  cbn [F_let].
  lazy delta [f].
  lazy beta iota zeta head.
  apply e.
Qed.

Theorem no_cycle n : match n with 0 => False | S n' => n = n' end -> False.
Proof. induction n; eauto. intros e. rewrite <- e in IHn. auto. Qed.

Theorem real_false : False.
Proof.
  eapply no_cycle.
  apply false.
  reflexivity.
Qed.
*)
