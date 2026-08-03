Require Import Ltac2.Ltac2.

Ltac2 Type exn ::= [ Regression_Test_Failure ].
Ltac2 check (b : bool) := if b then () else Control.throw Regression_Test_Failure.
Ltac2 check_eq_int_opt (a : int option) (b : int option) := check (Option.equal Int.equal a b).

Ltac2 Eval check_eq_int_opt (List.find_index_opt (Int.equal 2) [1; 2; 3; 2]) (Some 1).
Ltac2 Eval check_eq_int_opt (List.find_rev_index_opt (Int.equal 2) [1; 2; 3; 2]) (Some 3).
Ltac2 Eval check_eq_int_opt (List.find_index_opt (Int.equal 9) [1; 2; 3]) None.
Ltac2 Eval check_eq_int_opt (List.find_rev_index_opt (Int.equal 9) [1; 2; 3]) None.
Ltac2 Eval check_eq_int_opt (List.find_index_opt (fun _ => true) []) None.
Ltac2 Eval check (Int.equal (List.find_index (Int.equal 3) [1; 2; 3; 2]) 2).
Ltac2 Eval check (Int.equal (List.find_rev_index (Int.equal 1) [1; 2; 3; 2]) 0).
Fail Ltac2 Eval List.find_index (Int.equal 9) [1; 2; 3].
Fail Ltac2 Eval List.find_rev_index (Int.equal 9) ([] : int list).
