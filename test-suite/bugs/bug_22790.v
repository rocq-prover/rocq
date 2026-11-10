Definition T := Type.
Definition idT (X : T) : T := X.

Goal forall (B : T), idT B = B -> @None (idT B) = @None B.
Proof.
  intros B H.
  congruence.
Qed.

Set Universe Polymorphism.
Axiom c@{u} : nat -> nat.

Lemma foo (a b : nat) (H : a = b) : c a = c b.
Proof.
  change (c@{Set} a = c b).
  congruence.
Qed.
