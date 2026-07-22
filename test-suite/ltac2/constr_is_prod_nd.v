Require Import Ltac2.Ltac2.

Ltac2 Type exn ::= [ Regression_Test_Failure ].
Ltac2 check (b : bool) := if b then () else Control.throw Regression_Test_Failure.

Ltac2 Eval check (Constr.is_prod_nd constr:(nat -> nat)).
Ltac2 Eval check (Constr.is_prod_nd constr:(nat -> nat -> bool)).
Ltac2 Eval check (Bool.neg (Constr.is_prod_nd constr:(forall n : nat, n = n))).
Ltac2 Eval check (Constr.is_prod_nd constr:(forall _ : nat, nat)).
Ltac2 Eval check (Bool.neg (Constr.is_prod_nd constr:(fun n : nat => n))).
Ltac2 Eval check (Bool.neg (Constr.is_prod_nd constr:(0))).
