Declare ML Module "rocq-test-suite.attribute".

#[print]
Definition foo : True := I.

#[print]
Definition bar : False -> False := fun x => x.

Fail #[error]
Definition baz : False -> False := fun x => x.

(* Programmable-attribute hooks must also fire when a Lemma/Theorem is
   completed (at Qed/Defined), not only for Definition. *)
#[print]
Lemma lem : True.
Proof. exact I. Qed.

#[print]
Theorem thm : True.
Proof. exact I. Defined.

(* Mutual proofs: the #[print] hook fires once per declared constant. *)
Inductive even : nat -> Prop :=
| even_O : even 0
| even_S : forall n, odd n -> even (S n)
with odd : nat -> Prop :=
| odd_S : forall n, even n -> odd (S n).

#[print]
Lemma even_triv : forall n, even n -> True
with odd_triv : forall n, odd n -> True.
Proof. - intros; exact I. - intros; exact I. Qed.

(* The error hook fires at completion time, so it is Qed that must fail. *)
#[error]
Lemma lem_err : True.
Proof. exact I. Fail Qed.
Abort.

(* par marshals th summary, enforcing that it doesn't contain closures *)
Lemma parfoo : True /\ True.
Proof.
  split.
  par: exact I.
Defined.
