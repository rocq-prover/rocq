Section A.
  Context {A : Type}.
  Implicit Type (R : A -> A -> Prop).
  Definition flip R := (fun x y => R y x).
  Definition Reflexive R := forall x, R x x.
  Definition flip_Reflexive R : Reflexive R -> Reflexive (flip R) := fun H => H.
End A.

Goal exists (R : unit -> nat -> nat -> Prop) (t : unit), Reflexive (R t).
Proof.
  do 2 eexists.
  Fail eapply flip_Reflexive with (R := _ _).
Abort.
