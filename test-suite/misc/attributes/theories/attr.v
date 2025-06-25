Declare ML Module "rocq-test-suite.attribute".

#[print]
Definition foo : True := I.

#[print]
Definition bar : False -> False := fun x => x.

Fail #[error]
Definition baz : False -> False := fun x => x.

(* par marshals th summary, enforcing that it doesn't contain closures *)
Lemma parfoo : True /\ True.
Proof.
  split.
  par: exact I.
Defined.
