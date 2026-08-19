(* The "Not convertible" error should say which terms are not convertible. *)

Goal True.
Proof.
Fail change False.
Fail change (1 = 1).
Fail change ?x with (x -> x).
Abort.
