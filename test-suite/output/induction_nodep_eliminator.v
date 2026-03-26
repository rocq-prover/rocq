(** Verify that induction selects the non-dependent eliminator for
    non-dependent goals (and the dependent one for dependent goals),
    by inspecting the proof term via [Show Proof]. *)

Require Import Corelib.Init.Nat.


(** Non-dependent goal in Set: proof term should mention nat_rec. *)
Goal nat -> bool.
  intros n; induction n; exact true.
  Show Proof.
Abort.

(** Non-dependent goal in Prop: proof term should mention nat_ind. *)
Goal nat -> True.
  intros n; induction n; exact I.
  Show Proof.
Abort.

(** Dependent goal in Prop: proof term should mention nat_ind (dependent). *)
Goal forall n : nat, n + 0 = n.
  intros n. induction n.
  - Show Proof.
Abort.

Scheme Minimality for nat Sort Set.   (* registers nat_rec_nodep *)
Scheme Minimality for nat Sort Prop.  (* registers nat_ind_nodep *)

(** Non-dependent goal in Set: proof term should mention nat_rec_nodep. *)
Goal nat -> bool.
  intros n; induction n; exact true.
  Show Proof.
Abort.

(** Non-dependent goal in Prop: proof term should mention nat_ind_nodep. *)
Goal nat -> True.
  intros n; induction n; exact I.
  Show Proof.
Abort.

(** Dependent goal in Prop: proof term should mention nat_ind (dependent). *)
Goal forall n : nat, n + 0 = n.
  intros n. induction n.
  - Show Proof.
Abort.

Local Unset Elimination Schemes.
Local Set Universe Minimization ToSet.
Local Set Polymorphic Inductive Cumulativity.

Inductive list@{i|} (A : Type@{i}) : Type@{i} :=
| nil : list A
| cons : A -> list A -> list A.

Arguments nil {A}.
Arguments cons {A} _ _.

Scheme list_rect := Induction for list Sort Type.
Scheme list_ind := Induction for list Sort Type.
Scheme list_rec := Minimality for list Sort Type.

Definition for_all@{i j|} {A : Type@{i}} (P : A -> Type@{j}) (l : list A) : Type@{j} :=
  unit.

Definition list_sigma {A : Type} (P : A -> Type) (l : list A) (p : for_all P l)
  : list {x : A & P x}.
Proof.
  induction l as [|x l IHl] in p |- *.
  Show Proof.
Abort.
