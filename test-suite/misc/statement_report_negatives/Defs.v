(* Objects for misc/statement_report_negatives.sh, compiled with -noinit. *)

Inductive nat : Set := O : nat | S : forall _ : nat, nat.
Inductive same (A : Type) (x : A) : forall _ : A, Prop := same_refl : same A x x.

Axiom ax : nat.
Axiom extra : nat.
Definition uses_ax : nat := ax.

Module Type SIG.
  Parameter thm : nat.
End SIG.

(* The signature hides [thm]'s body, which reaches [ax] only through the
   transparent [uses_ax]: an axiom list of [thm]'s direct bodiless
   references is empty. *)
Module Sealed : SIG.
  Definition thm := uses_ax.
End Sealed.

(* [helper] exists only in the implementation: the environment does not
   hold it. *)
Module Helper : SIG.
  Definition helper := uses_ax.
  Definition thm := helper.
End Helper.

(* An axiom that exists only in the implementation. *)
Module HiddenAxiom : SIG.
  Axiom hidden : nat.
  Definition thm := hidden.
End HiddenAxiom.

(* An inductive that exists only in the implementation. *)
Module HiddenInductive : SIG.
  Inductive t : Set := c : t.
  Definition thm := match c with c => uses_ax end.
End HiddenInductive.
