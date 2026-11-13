From Corelib Require Import PrimInt63 PrimArray.

(* Wrong normal form: expected [fun x _ => x], lazy returns [fun _ y => y]. *)
Abbreviation term := (fun x : bool => (fun (a : array bool) (y : nat) => get a 0) [| x | x |]).

Definition f : bool -> nat -> bool := Eval lazy in term.
Definition g : bool -> nat -> bool := Eval cbv  in term.

(* Kernel accepts an ill-typed term: [y = y] is taken for [x = y]. *)
Definition T (a : array bool) : Prop := forall y : bool, get a 0 = y.

Lemma bad : forall x : bool, T [| x | x |].
Proof.
  exact_no_check (fun (x y : bool) => @eq_refl bool y).
  Fail Qed.
Abort.

(* Theorem boom : False. *)
(* Proof. *)
(*   exact (match bad true false in _ = b return (if b then True else False) *)
(*          with eq_refl => I end). *)
(* Qed. *)
(* Print Assumptions boom. (* only array axioms *) *)
