(* The unification of tactics on the projections of a record which has no
   canonical instance: a projection is reduced at once, as it used to be, so
   that no argument of a half-unfolded projection is unified before the
   projection is reduced. *)
Set Primitive Projections.

Record Fam (A : Type) := { fam : A -> Type }.
Definition const_fam (A B : Type) : Fam A := {| fam := fun _ => B |}.

Goal forall (X Y Z : Type) (g : X -> Y) (f h : Y -> Z)
    (q : forall y : Y, @eq (fam Y (const_fam Y Z) y) (f y) (h y)) (x : X),
    @eq (fam X (const_fam X Z) x) (f (g x)) (h (g x)).
Proof.
  intros X Y Z g f h q x.
  apply q.
Qed.
