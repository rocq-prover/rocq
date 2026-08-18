Require Import Extraction.

Polymorphic Lemma m1@{s;u} (A : Type@{s;u}) (a : A) (f : A -> nat) : nat.
Proof.
  exact (f a).
Qed.

Recursive Extraction m1.
