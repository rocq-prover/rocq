Require Import Ltac2.Ltac2.

Ltac2 Type exn ::= [ Regression_Test_Failure ].
Ltac2 check (b : bool) := if b then () else Control.throw Regression_Test_Failure.

Ltac2 Eval check (Int.equal (String.length_common_prefix "abcd" "abef") 2).
Ltac2 Eval check (Int.equal (String.length_common_prefix "xyz" "abc") 0).
Ltac2 Eval check (String.equal (String.common_prefix "abcd" "abef") "ab").
Ltac2 Eval check (String.equal (String.common_prefix "abc" "abcdef") "abc").
Ltac2 Eval check (Option.equal String.equal (String.strip_prefix "ab" "abcd") (Some "cd")).
Ltac2 Eval check (Option.equal String.equal (String.strip_prefix "abcd" "abcd") (Some "")).
Ltac2 Eval check (Option.equal String.equal (String.strip_prefix "b" "abcd") None).
Ltac2 Eval check (Option.equal String.equal (String.strip_prefix "abcde" "abcd") None).
Ltac2 Eval check (String.equal (String.replace_char (String.get "," 0) "; " "a,b,c") "a; b; c").
Ltac2 Eval check (String.equal (String.replace_char (String.get "," 0) "" ",a,") "a").
Ltac2 Eval check (String.equal (String.replace_char (String.get "," 0) "x" "abc") "abc").
