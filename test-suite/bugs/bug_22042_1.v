Set Definitional UIP.
Inductive test : nat -> SProp := T : test 0.
Axiom TT : SProp -> SProp.

Definition blo (A : nat -> _) (x : A 0) (y:nat) (e:test y)
  := let a := match e with T => x end in TT (A 0).
