Fail Inductive foo5@{s; |} (A:Type@{s;Set}) : Prop := Foo5 (_ : A).
(* Anomaly
"File "vernac/comInductive.ml", line 482, characters 10-16: Assertion failed."
Please report at http://rocq-prover.org/bugs/. *)
