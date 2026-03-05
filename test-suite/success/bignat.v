Register nat as kernel.ind_nat.

(* very important: printing with number notations currently very slow *)
Set Printing All.

Time Eval cbv in 5000000.
(* without bignat, stack overflows
   with bignat, 0.8s
   (time seems about linear in n, ie exponential in the size of the decimal representation)
*)

Time Eval cbv in 1000 * 1000.
(* without bignat, stack overflows
   with bignat, 0.1s *)

Register Nat.mul as cbv.mul.

Time Eval cbv in 1000 * 1000.
(* instant *)

Time Eval cbv in 200 * 200 * 200 * 200 * 200 * 200 * 200 * 200.
(* instant *)

Register Nat.tail_mul as cbv.tail_mul.
Time Eval cbv in 5000000.
(* instant *)
Time Eval cbv in 50000000.
(* also instant *)
Time Eval cbv in 500000000000000000000000000.
(* still instant *)

Definition pred n := match n with S k => k | O => O end.

Check eq_refl 0 : pred (pred 1) = 0.

Time Eval lazy in pred ltac:(let c := eval cbv in 500000000 in exact c).
(* instant (but big + 1 would stack overflow) *)

Fixpoint mymul n m :=
  match n with
  | O => O
  | S p => m + mymul p m
  end.

Notation "x ** y" := (mymul x y) (at level 41, right associativity).

Register Nat.add as cbv.add.

Time Eval cbv in 200 ** 200000000.
(* instant *)

Time Eval cbv in 200 ** 200 ** 200 ** 200 ** 200 ** 200 ** 200 ** 200.
(* right associativity very important here: it means we have 200 * 7 recursions in mymul
   instead of 200 ^ 7 *)
