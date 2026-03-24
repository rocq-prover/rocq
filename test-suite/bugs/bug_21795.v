CoInductive strm := mk { s : strm }.

CoFixpoint f1 := mk f1.
Definition f2 := cofix f2 := f1.

Fixpoint bli (n:nat) :=
  match f2 with mk _ => fun _ => n end bli.
(* Anomaly "File "kernel/inductive.ml", line 1526, characters 65-71: Assertion failed." *)
