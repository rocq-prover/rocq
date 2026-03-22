(** Test setoid rewriting with forall_relation. *)

From Corelib Require Import Morphisms.

Axiom K : nat -> nat -> nat -> Type.
Axiom T : nat -> forall n1 n2 n3, K n1 n2 n3 -> Prop.

Instance T_Proper : Proper (le ==> forallR n1 n2 n3, eq ==> Basics.impl)%signature T.
Admitted.

Lemma test i j (Hle : i <= j) n1 n2 n3 (k : K n1 n2 n3) (H : T i n1 n2 n3 k) : T j n1 n2 n3 k.
Proof.
  rewrite <-Hle.
  exact H.
Qed.
