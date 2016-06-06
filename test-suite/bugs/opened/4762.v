Inductive myand (P Q : Prop) := myconj : P -> Q -> myand P Q.

Lemma foo P Q R : R = myand P Q -> P -> Q -> R.
Proof. intros ->; constructor; auto. Qed.

Hint Extern 0 (myand _ _) => eapply foo; [reflexivity| |] : test1.

Goal forall P Q R : Prop, P -> Q -> R -> myand P (myand Q R).
Proof.
  intros.
  Fail solve [ eauto with test1 ]. (* does not solve the goal, but it should *)
  auto with test1. (* remove this line when the above sovles the goal *)
Qed.

Hint Extern 0 =>
  match goal with
  | |- myand _ _ => eapply foo; [reflexivity| |]
  end : test2.

Goal forall P Q R : Prop, P -> Q -> R -> myand P (myand Q R).
Proof.
  intros.
  eauto with test2. (* works *)
Qed.
