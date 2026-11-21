Require Import ssreflect.

Lemma bla (f g : nat -> nat) : f (g (1 + 1)) = f (g 2).
Proof.
Fail congr (_ (_ _)).
do 2 congr (_ _).
Qed.
