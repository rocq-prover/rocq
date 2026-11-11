Set Primitive Projections.

Section S.
  Variable A : Type.
  Record R (n : nat) (m := S n) := { f3 : A }.
End S.

Definition r : R nat 0 := Build_R nat 0 0.

Definition any := fun P : Type => r.(f3 nat 0).
Check any : forall P : Type, nat.
(* used to be [forall P : Type, P] *)
