Module Type T.
  Inductive foo := { x : nat } with bar := { y : nat }.
End T.
Module M <: T.
  Inductive foo := { x : nat } with bar := { y : nat }.
End M.
(* Anomaly "File "kernel/subtyping.ml", line 205, characters 4-10: Assertion failed." *)
