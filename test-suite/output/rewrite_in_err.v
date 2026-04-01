Require Export Morphisms.

Axiom T : nat -> Prop.

Lemma test i j (Hle : i <= j) (H : T j) : T j.
Proof.
  Fail rewrite Hle in H.
(* The command has indeed failed with message:
   Found no subterm matching "i" in the current goal. *)
Abort.
