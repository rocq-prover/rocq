Fixpoint foo (n:nat) : forall A : Type@{_}, A -> A.
Proof.
  Fail exact (fun (A:Set) a => a).
  exact (fun A a => a).
Qed.

#[refine] Fixpoint bar (n:nat) : forall A : Type@{_}, A -> A := _.
Proof.
  Fail exact (fun (A:Set) a => a).
  exact (fun A a => a).
Qed.
