Section S.
  Context (A : Type).

  Fail Context (A : Type).
  (* Error: Anomaly "File "kernel/environ.ml", line 207, characters 2-8: Assertion failed." *)

  Fail Context (x:nat) (x:nat).
End S.
