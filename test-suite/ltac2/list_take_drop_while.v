Require Import Ltac2.Ltac2.

Ltac2 Type exn ::= [ Regression_Test_Failure ].
Ltac2 check (b : bool) := if b then () else Control.throw Regression_Test_Failure.
Ltac2 check_eq_l (a : int list) (b : int list) := check (List.equal Int.equal a b).

Ltac2 Eval check_eq_l (List.take_while (Int.gt 3) [1; 2; 3; 1]) [1; 2].
Ltac2 Eval check_eq_l (List.drop_while (Int.gt 3) [1; 2; 3; 1]) [3; 1].
Ltac2 Eval check_eq_l (List.take_while (Int.gt 3) []) [].
Ltac2 Eval check_eq_l (List.drop_while (Int.gt 3) []) [].
Ltac2 Eval check_eq_l (List.take_while (Int.gt 9) [1; 2]) [1; 2].
Ltac2 Eval check_eq_l (List.drop_while (Int.gt 9) [1; 2]) [].
Ltac2 Eval
  let (pre, rest) := List.take_drop_while (Int.gt 3) [1; 2; 3; 1] in
  check_eq_l pre [1; 2]; check_eq_l rest [3; 1].
Ltac2 Eval
  let (pre, rest) := List.take_drop_while (Int.gt 3) [] in
  check_eq_l pre []; check_eq_l rest [].
