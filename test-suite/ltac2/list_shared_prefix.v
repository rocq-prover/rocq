Require Import Ltac2.Ltac2.

Ltac2 Type exn ::= [ Regression_Test_Failure ].
Ltac2 check (b : bool) := if b then () else Control.throw Regression_Test_Failure.
Ltac2 check_eq_l (a : int list) (b : int list) := check (List.equal Int.equal a b).

Ltac2 Eval
  let (pre, rest) := List.shared_prefix Int.equal [1; 2; 3] [1; 2; 4; 5] in
  let (r1, r2) := rest in
  check_eq_l pre [1; 2]; check_eq_l r1 [3]; check_eq_l r2 [4; 5].
Ltac2 Eval
  let (pre, rest) := List.shared_prefix Int.equal [1; 2] [1; 2] in
  let (r1, r2) := rest in
  check_eq_l pre [1; 2]; check_eq_l r1 []; check_eq_l r2 [].
Ltac2 Eval
  let (pre, rest) := List.shared_prefix Int.equal [] [1] in
  let (r1, r2) := rest in
  check_eq_l pre []; check_eq_l r1 []; check_eq_l r2 [1].
Ltac2 Eval
  let (pre, _) := List.shared_prefix_full Int.equal [1; 2; 3] [1; 9] in
  check (Int.equal (List.length pre) 1).
