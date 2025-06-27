Set Universe Polymorphism.
Set Primitive Projections.

Structure S := { carrier :> Type; val : carrier }.

Canonical Structure default@{i j} : S@{j} := {| carrier := Type@{i}; val := nat |}.

Definition test (s : S) : carrier s := val s.

(** We want to force a CS resolution for default, so a problem carrier ?S = Type *)

Axiom fn : forall x : Type, True.

Lemma foo@{i} : True.
  apply fn. apply (test@{i} _).
Qed.

Lemma foo'@{i} : True.
  apply fn. refine (test@{i} _).
Qed.
