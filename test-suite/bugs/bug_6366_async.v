(* -*- coq-prog-args: ("-async-proofs" "on"); -*- *)

Set Implicit Arguments.

Record dynamic := dyn { dyn_type : Type; dyn_value : dyn_type }.

Lemma dyn_inj_type : forall A1 A2 (x1:A1) (x2:A2), dyn x1 = dyn x2 -> A1 = A2.
Proof.
now intros A1 A2 x1 x2 [= e1 e2].
Qed.

Lemma foo : Type.
Proof.
abstract exact Set.
Qed.
