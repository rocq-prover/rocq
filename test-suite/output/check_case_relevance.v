From Ltac2 Require Import Ltac2 Constr.
Import Constr.Unsafe.

Ltac2 bad p i :=
  (* the incorrect relevance will be dropped when moving to kernel representation
     so it doesn't cause an inconsistency *)
  let badx := Binder.unsafe_make None Relevance.irrelevant 'nat in
  let br := make (Lambda badx (make (Lambda badx i))) in
  let ind := match reference:(prod) with Std.IndRef ind => ind | _ => Control.throw Assertion_failure end in
  make (Case (case ind) ('(fun (_:nat * nat) => nat), Relevance.relevant) NoInvert p [|br|]).

Definition badfst (p:nat * nat) := ltac2:(let x := bad '&p (make (Rel 2)) in exact $x).
Definition badsnd (p:nat * nat) := ltac2:(let x := bad '&p (make (Rel 1)) in exact $x).

Definition bad p : badfst p = badsnd p.
Proof.
  Fail exact eq_refl.
  ltac1:(exact_no_check (eq_refl (badfst p))).
  Fail Defined.
Abort.
