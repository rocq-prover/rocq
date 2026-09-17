Require Import Corelib.Program.Tactics.

(* The warning is disabled by default. *)
Lemma default_disabled : True.
Proof.
Admitted.

Set Warnings "admitted-proof".

Lemma admitted_lemma : True.
Proof.
Admitted.

Program Definition admitted_obligation : nat := _.
Next Obligation.
Admitted.

Program Definition admitted_obligations : nat * nat := (_, _).
Admit Obligations of admitted_obligations.

(* As an error, the warning must not admit the proof. *)
Set Warnings "+admitted-proof".
Lemma rejected_admission : True.
Proof.
Fail Admitted.
Set Warnings "admitted-proof".
exact I.
Qed.
