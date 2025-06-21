Module M.
  Axiom foo : bool.
End M.
Import M.

Ltac bli H := inversion H.

Goal forall n m:nat, Some n = Some m -> True /\ True.
  intros n m.
  (* NB bug only occurred with intro not intros *)
  intro foo; split; bli foo.
Abort.
