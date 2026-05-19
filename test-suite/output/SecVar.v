Section S.
  Variables a b : nat.
  Variable H : a = b.

  Set Printing Variables Status.

  Goal True.
  Proof.
    Show.
    apply eq_sym in H.
    Show.
    rename b into y.
    Show.
  Abort.
End S.
