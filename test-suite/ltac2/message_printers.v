Require Import Ltac2.Ltac2.

Ltac2 Type exn ::= [ Regression_Test_Failure ].
Ltac2 check (b : bool) := if b then () else Control.throw Regression_Test_Failure.
Ltac2 check_msg (m : message) (s : string) := check (String.equal (Message.to_string m) s).

Ltac2 Eval check (String.equal (Bool.to_string true) "true").
Ltac2 Eval check (String.equal (Bool.to_string false) "false").
Ltac2 Eval check_msg (Message.of_bool true) "true".
Ltac2 Eval check_msg (Message.of_list Message.of_int [1; 2; 3]) "1; 2; 3".
Ltac2 Eval check_msg (Message.of_list Message.of_int [1]) "1".
Ltac2 Eval check_msg (Message.of_list Message.of_int []) "".
Ltac2 Eval check_msg (Message.of_list_with_sep (Message.of_string ",") Message.of_int [1; 2]) "1,2".
Ltac2 Eval check_msg (Message.of_option Message.of_int (Some 5)) "Some 5".
Ltac2 Eval check_msg (Message.of_option Message.of_int None) "None".
