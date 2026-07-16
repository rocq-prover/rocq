Require Import Ltac2.Ltac2.

Ltac2 Type exn ::= [ Regression_Test_Failure ].
Ltac2 check (b : bool) := if b then () else Control.throw Regression_Test_Failure.

Ltac2 Eval check (Constr.is_prod constr:(nat -> nat)).
Ltac2 Eval check (Constr.is_prod constr:(forall n : nat, n = n)).
Ltac2 Eval check (Bool.neg (Constr.is_prod constr:(fun n : nat => n))).
Ltac2 Eval check (Constr.is_lambda constr:(fun n : nat => n)).
Ltac2 Eval check (Bool.neg (Constr.is_lambda constr:(nat -> nat))).
Ltac2 Eval check (Constr.is_letin constr:(let x := 1 in x)).
Ltac2 Eval check (Bool.neg (Constr.is_letin constr:(S 0))).
Ltac2 Eval check (Constr.is_app constr:(S 0)).
Ltac2 Eval check (Bool.neg (Constr.is_app constr:(S))).
Ltac2 Eval check (Constr.is_case constr:(match 0 with 0 => 0 | S n => n end)).
Ltac2 Eval check (Bool.neg (Constr.is_case constr:(S 0))).
Ltac2 Eval check (Constr.is_rel (Constr.Unsafe.make (Constr.Unsafe.Rel 1))).
Ltac2 Eval check (Bool.neg (Constr.is_rel constr:(0))).
Ltac2 Eval check (Bool.neg (Constr.is_meta constr:(0))).
Ltac2 Eval check (Bool.neg (Constr.is_cast constr:(S 0))).
