Require Import Ltac2.Ltac2.

Ltac2 Type exn ::= [ Regression_Test_Failure ].
Ltac2 check (b : bool) := if b then () else Control.throw Regression_Test_Failure.

Ltac2 Eval check (Constr.is_prop constr:(Prop)).
Ltac2 Eval check (Bool.neg (Constr.is_prop constr:(Set))).
Ltac2 Eval check (Bool.neg (Constr.is_prop constr:(Type))).
Ltac2 Eval check (Constr.is_set constr:(Set)).
Ltac2 Eval check (Bool.neg (Constr.is_set constr:(Prop))).
Ltac2 Eval check (Constr.is_sprop constr:(SProp)).
Ltac2 Eval check (Bool.neg (Constr.is_sprop constr:(Prop))).
Ltac2 Eval check (Constr.is_type constr:(Type)).
Ltac2 Eval check (Bool.neg (Constr.is_type constr:(Prop))).
Ltac2 Eval check (Bool.neg (Constr.is_type constr:(Set))).
Ltac2 Eval check (Bool.neg (Constr.is_type constr:(SProp))).
Ltac2 Eval check (Bool.neg (Constr.is_type constr:(nat))).
Ltac2 Eval check (Constr.is_type_or_set constr:(Set)).
Ltac2 Eval check (Constr.is_type_or_set constr:(Type)).
Ltac2 Eval check (Bool.neg (Constr.is_type_or_set constr:(Prop))).
Ltac2 Eval check (Bool.neg (Constr.is_prop constr:(0))).
