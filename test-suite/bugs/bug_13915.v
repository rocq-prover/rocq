Require Import ssreflect.

Set Warnings "+remaining-shelved-goals".

Lemma foo {x : Prop} : x -> x.
Proof. eauto. Qed.

(* Sanity check: direct [apply: foo] does not leave a shelved goal. *)
Goal True -> True.
Proof.
  apply: foo.
  Unshelve.
Qed.

Tactic Notation "use" open_constr(H) := apply: H.
Tactic Notation "use_apply" open_constr(H) := apply H.
Tactic Notation "use_eapply" open_constr(H) := eapply H.

(* Going through [Tactic Notation] with [open_constr] should behave like the
   direct ssreflect tactic: the implicit argument evar created while reading
   [H] must be consumed when [apply: H] instantiates it. *)
Goal True -> True.
Proof.
  use foo.
Qed.

(* Ordinary Ltac apply/eapply are controls documenting the expected behavior. *)
Goal True -> True.
Proof.
  use_apply foo.
Qed.

Goal True -> True.
Proof.
  use_eapply foo.
Qed.

Lemma needs {P : Prop} : P -> True.
Proof. auto. Qed.

(* Real premises should still be exposed as focused goals, not hidden as
   shelved or otherwise invisible evars. *)
Goal True.
Proof.
  apply: needs.
  exact I.
Qed.

Goal True.
Proof.
  use needs.
  exact I.
Qed.

(* Incomplete applications must still fail to close. *)
Goal True.
Proof.
  apply: needs.
  Fail Qed.
Abort.

Goal True.
Proof.
  use needs.
  Fail Qed.
Abort.
