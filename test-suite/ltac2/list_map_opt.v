Require Import Ltac2.Ltac2.

Ltac2 Type exn ::= [ Regression_Test_Failure ].
Ltac2 check (b : bool) := if b then () else Control.throw Regression_Test_Failure.

Ltac2 Eval check (Option.equal (List.equal Int.equal)
  (List.map_opt (fun x => if Int.gt x 0 then Some (Int.add x 1) else None) [1; 2; 3])
  (Some [2; 3; 4])).
Ltac2 Eval check (Option.equal (List.equal Int.equal)
  (List.map_opt (fun x => if Int.gt x 1 then Some x else None) [1; 2; 3])
  None).
Ltac2 Eval check (Option.equal (List.equal Int.equal)
  (List.map_opt (fun (x : int) => (None : int option)) [])
  (Some [])).
