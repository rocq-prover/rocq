Require Import Ltac2.Ltac2.

Ltac2 Type exn ::= [ Regression_Test_Failure ].
Ltac2 check (b : bool) := if b then () else Control.throw Regression_Test_Failure.

(* immediate subterms of [S 0] are [S] and [0] *)
Ltac2 Eval check (Int.equal (Constr.Unsafe.fold (fun n _ => Int.add n 1) 0 constr:(S 0)) 2).
(* immediate subterms of [fun x : nat => x] are [nat] and [Rel 1] *)
Ltac2 Eval check (Int.equal (Constr.Unsafe.fold (fun n _ => Int.add n 1) 0 constr:(fun x : nat => x)) 2).
Ltac2 Eval check (Int.equal (Constr.Unsafe.fold (fun n _ => Int.add n 1) 0 constr:(0)) 0).
(* fold_with_binders: sum the binder depths at which subterms occur *)
Ltac2 Eval check (Int.equal
  (Constr.Unsafe.fold_with_binders (fun n _ => Int.add n 1)
     (fun n acc _ => Int.add acc n) 0 0 constr:(fun x : nat => S x))
  1). (* [nat] at depth 0, [S x] at depth 1 *)

Goal forall x : nat, x = x -> True.
Proof.
  intros x h.
  let t := Constr.type (Control.hyp @h) in check (Constr.has_var t).
  check (Bool.neg (Constr.has_var constr:(S 0))).
  exact I.
Qed.

Ltac2 Eval check (Constr.has_fix_or_cofix constr:(fix f (n : nat) : nat := 0)).
Ltac2 Eval check (Constr.has_fix_or_cofix constr:(S ((fix f (n : nat) : nat := 0) 0))).
Ltac2 Eval check (Bool.neg (Constr.has_fix_or_cofix constr:(S 0))).
Ltac2 Eval check (Constr.is_fix_or_cofix constr:(fix f (n : nat) : nat := 0)).
Ltac2 Eval check (Constr.has_of_is Constr.is_ind constr:(S 0 = 1)).
