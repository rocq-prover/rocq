Set Proof Using Clear Unused.
Require Import Derive.
Derive A in (A = 1) as B.
Proof using Type.
  unfold A;reflexivity.
Qed.

Section S.
  Variable n : nat.

  Derive (A':nat) in nat as B'.
  Proof using .
    Unshelve.
    Fail all:exact n.
  Abort.

  Derive (A':nat) in nat as B'.
  Proof using n.
    Unshelve.
    all:exact n.
  Qed.

  Variable A : Type.

  Derive X : A -> A in (X = X) as H.
  Proof using Type*.
    reflexivity.
    Unshelve.
    exact (fun x => x).
  Qed.
End S.
