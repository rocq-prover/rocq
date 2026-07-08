Require Import Ltac2.Ltac2.

Ltac2 Type exn ::= [ Regression_Test_Failure ].
Ltac2 check (b : bool) := if b then () else Control.throw Regression_Test_Failure.

Ltac2 Eval check (Int.equal (Int.min 1 2) 1).
Ltac2 Eval check (Int.equal (Int.min 2 1) 1).
Ltac2 Eval check (Int.equal (Int.min 1 1) 1).
Ltac2 Eval check (Int.equal (Int.min (Int.neg 1) 1) (Int.neg 1)).
Ltac2 Eval check (Int.equal (Int.max 1 2) 2).
Ltac2 Eval check (Int.equal (Int.max 2 1) 2).
Ltac2 Eval check (Int.equal (Int.max (Int.neg 3) (Int.neg 5)) (Int.neg 3)).
