From Ltac2 Require Import Ltac2.
From Tuto4 Require Import Loader.

(* try out our "question" primitive *)
Ltac2 Eval question 2. (* false *)
Ltac2 Eval question 42. (* true *)

(* try out our "tuto_exact" primitive *)
Goal True.
  Fail tuto_exact '0.
  tuto_exact 'I.
Qed.

(* try out our custom type functions *)
Ltac2 Eval ind_or_a A.
Ltac2 Eval ind_or_a (B '0).
Ltac2 Eval ind_or_a (B 'nat).

Goal nat -> nat.
  intros x.
  Ltac2 Eval check_in_goal @x.
  Ltac2 Eval check_in_goal @y.
Abort.

(* try out our custom2 functions *)
Ltac2 Eval mk_custom2 2 4. (* our printer works *)

Ltac2 Eval sum2 (mk_custom2 2 4).
