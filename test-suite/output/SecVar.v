Section S.
  Variables a b : nat.
  Variable H : a = b.

  Set Printing Variables Status.

  Goal True.
  Proof.
    About a, b, H.
    Show.
    apply eq_sym in H.
    About a, b, H.
    Show.
    rename b into y.
    About a, y, H.
    Show.
  Abort.
End S.
