Require Import HintAttr.HintAttr.

Create HintDb mydb.

(* On a Lemma: registers [foo] in [mydb] with cost 3, exported. *)
#[hint(db=mydb, cost="3", visibility=export)]
Lemma foo : True.
Proof. exact I. Qed.

(* The hint must now be usable from [mydb]. *)
Goal True.
Proof. solve [ auto with mydb ]. Qed.

(* On a Definition, with a different visibility and no explicit cost. *)
#[hint(db=mydb, visibility=global)]
Definition bar : True := I.

Goal True.
Proof. solve [ auto with mydb ]. Qed.

(* Default cost and default visibility (omitted keys). *)
Definition P := True.
#[hint(db=mydb)]
Lemma p_proof : P.
Proof. exact I. Qed.

Goal P.
Proof. solve [ auto with mydb ]. Qed.

(* Error handling: missing [db]. *)
Fail #[hint(cost="1")]
Definition baz : True := I.

(* Error handling: non-integer cost. *)
Fail #[hint(db=mydb, cost="oops")]
Definition qux : True := I.

(* Error handling: bad visibility. *)
Fail #[hint(db=mydb, visibility=sometimes)]
Definition quux : True := I.

(* Error handling: unknown sub-key. *)
Fail #[hint(db=mydb, color="blue")]
Definition corge : True := I.
