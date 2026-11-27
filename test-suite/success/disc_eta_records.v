(* Constructors of primitive records with eta convert to any term of their
   type, so dnets must not index transparent constants unfolding to them. *)

Set Primitive Projections.

Record Category := { obj : Type; hom : obj -> obj -> Type }.

Definition op (C : Category) : Category :=
  {| obj := obj C; hom := fun x y => hom C y x |}.

Class Terminal (C : Category) := { one : obj C }.

Goal forall C (H : Terminal C), Terminal (op (op C)).
Proof. intros. Succeed exact _. typeclasses eauto. Qed.

Record Ring := { car : Type; mul : car -> car -> car }.

Definition rng_op (R : Ring) : Ring :=
  {| car := car R; mul := fun x y => mul R y x |}.

Class IsInvertible (R : Ring) (x : car R) := { inv : car R }.

Goal forall (R : Ring) (x : car R) (H : IsInvertible R x), IsInvertible (rng_op (rng_op R)) x.
Proof. intros. typeclasses eauto. Qed.
