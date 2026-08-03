Require Import Ltac2.Ltac2.

Ltac2 Type exn ::= [ Regression_Test_Failure ].
Ltac2 check (b : bool) := if b then () else Control.throw Regression_Test_Failure.
Ltac2 check_eq_sl (a : string list) (b : string list) := check (List.equal String.equal a b).
Ltac2 comma () : char := String.get "," 0.

Ltac2 Eval check (Char.is_space (String.get " " 0)).
Ltac2 Eval check (Bool.neg (Char.is_space (String.get "a" 0))).
Ltac2 Eval check_eq_sl (String.split_on_char (comma ()) "a,b,c") ["a"; "b"; "c"].
Ltac2 Eval check_eq_sl (String.split_on_char (comma ()) "a,,c,") ["a"; ""; "c"; ""].
Ltac2 Eval check_eq_sl (String.split_on_char (comma ()) "") [""].
Ltac2 Eval check_eq_sl (String.split_on_char (comma ()) ",") [""; ""].
Ltac2 Eval check (String.equal (String.concat (String.make 1 (comma ())) (String.split_on_char (comma ()) "x,y,")) "x,y,").
Ltac2 Eval check (String.equal (String.trim "  a b  ") "a b").
Ltac2 Eval check (String.equal (String.trim "a") "a").
Ltac2 Eval check (String.equal (String.trim "   ") "").
Ltac2 Eval check (String.equal (String.trim "") "").
