Section AR.
  Parameter A: Type.
  Parameter op: A -> A -> A.

  Parameter assoc: forall a0 a1 a2: A,
      op (op a0 a1) a2 = op a0 (op a1 a2).

  Create Rewrite HintDb op.
  Hint Rewrite assoc : op.

  Goal forall a0 a1 a2 a3: A,
      op (op (op a0 a1) a2) a3 =
        op a0 (op a1 (op a2 a3)).
  Proof.
    intros.
    autorewrite with op.
    autorewrite <- with op.
    reflexivity.
  Qed.
End AR.
