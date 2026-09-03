Require Import Ltac2.Ltac2.

Ltac2 Type exn ::= [ Regression_Test_Failure ].
Ltac2 check (b : bool) := if b then () else Control.throw Regression_Test_Failure.
Ltac2 check_eq_l (a : int list) (b : int list) := check (List.equal Int.equal a b).

Ltac2 Eval check_eq_l (List.firstn_relaxed 2 [1; 2; 3]) [1; 2].
Ltac2 Eval check_eq_l (List.firstn_relaxed 5 [1; 2; 3]) [1; 2; 3].
Ltac2 Eval check_eq_l (List.firstn_relaxed 0 [1; 2; 3]) [].
Ltac2 Eval check_eq_l (List.skipn_relaxed 2 [1; 2; 3]) [3].
Ltac2 Eval check_eq_l (List.skipn_relaxed 5 [1; 2; 3]) [].
Ltac2 Eval check_eq_l (List.skipn_relaxed 0 [1; 2; 3]) [1; 2; 3].
Fail Ltac2 Eval List.firstn_relaxed (Int.neg 1) [1; 2; 3].
Fail Ltac2 Eval List.skipn_relaxed (Int.neg 1) [1; 2; 3].
