(* Was failing with anomaly List.chop in 8.15 and was running for very long in 9.0 *)
(* This tests abbreviations with more projection parameters than allowed *)
Class my_class := {
    my_class_car : Type;
    my_class_field_aux : my_class_car -> nat
}.

Notation my_class_field := (@my_class_field_aux _).

Fail Timeout 10 Definition my_test {MC : my_class} (x : my_class_car) : nat :=
  x.(my_class_field).
