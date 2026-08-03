Require Import Ltac2.Ltac2.

Ltac2 Type exn ::= [ Regression_Test_Failure ].
Ltac2 check (b : bool) := if b then () else Control.throw Regression_Test_Failure.
Ltac2 c (s : string) : char := String.get s 0.

Ltac2 Eval check (String.starts_with "He" "Hello").
Ltac2 Eval check (String.starts_with "" "Hello").
Ltac2 Eval check (String.starts_with "" "").
Ltac2 Eval check (Bool.neg (String.starts_with "hello" "He")).
Ltac2 Eval check (Bool.neg (String.starts_with "eH" "Hello")).
Ltac2 Eval check (String.ends_with "lo" "Hello").
Ltac2 Eval check (String.ends_with "" "Hello").
Ltac2 Eval check (Bool.neg (String.ends_with "Hello!" "lo")).
Ltac2 Eval check (Int.equal (String.index "banana" (c "a")) 1).
Ltac2 Eval check (Int.equal (String.index_from "banana" 2 (c "a")) 3).
Ltac2 Eval check (Option.equal Int.equal (String.index_opt "banana" (c "z")) None).
Ltac2 Eval check (Option.equal Int.equal (String.index_from_opt "banana" 6 (c "a")) None).
Fail Ltac2 Eval String.index "banana" (c "z").
Fail Ltac2 Eval String.index_from_opt "banana" 7 (c "a").
Fail Ltac2 Eval String.index_from_opt "banana" (Int.neg 1) (c "a").
