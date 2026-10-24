(* Model constants and trusted statements for misc/statement_report_negatives.sh. *)

Require Import StmtNeg.Defs.

Parameter trusted : same nat uses_ax uses_ax.
Parameter trusted_thm : same nat Sealed.thm Sealed.thm.

(* Sealed modules: each closure is [ax], or [HiddenAxiom.hidden]. *)
Definition sealed : same nat Sealed.thm Sealed.thm := same_refl nat Sealed.thm.
Definition helper : nat := Helper.thm.
Definition hidden_axiom : nat := HiddenAxiom.thm.
Definition hidden_inductive : nat := HiddenInductive.thm.

(* One axiom more than [clean], at the same type. *)
Definition clean : same nat uses_ax uses_ax := same_refl nat uses_ax.
Definition dirty : same nat uses_ax uses_ax :=
  match extra with O => same_refl nat uses_ax | S _ => same_refl nat uses_ax end.

(* A neighbouring statement, and a statement convertible to [trusted]'s. *)
Definition near : same nat (S uses_ax) (S uses_ax) := same_refl nat (S uses_ax).
Definition conv : same nat ax ax := same_refl nat ax.

(* Universes. *)
Polymorphic Definition pmodel@{u} : forall _ : Type@{u}, Type@{u} := fun A => A.
Parameter ptrusted : forall _ : Type, Type.
Polymorphic Parameter ptrusted_poly@{u} : forall _ : Type@{u}, Type@{u}.
Polymorphic Definition pmodel_lt@{u v | u < v} : forall _ : Type@{u}, Type@{v} := fun A => A.
Polymorphic Parameter ptrusted_lt@{u v} : forall _ : Type@{u}, Type@{v}.
