From Corelib Require Import Setoid Morphisms.

Definition eqT (x y : nat) : Type := x = y.

Parameter mul : nat -> nat -> nat.
#[local] Instance mul_comp : Proper (eq ==> eq ==> eq) mul.
Proof. Admitted.

Lemma test (x y y' : nat) (H : eqT y y') : mul x y = mul x y'.
Proof. rewrite H. reflexivity. Qed.
