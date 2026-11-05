Axiom ap : forall (A : Type) (P Q : A -> Type) (x : A) (f : forall x0 : A, P x0 -> Q x0) (z : P x),
    f x z = f x z.

Goal forall (B : Type) (U : Type -> Type) (F : B -> U B) (R : Prop), R.
Proof.
  intros.
  Fail rewrite <- ap with (f := F).
  Fail rewrite ap with (f := F).
Abort.

Axiom equal_f : forall {A B : Type} {f g : A -> B}, f = g -> forall x : A, f x = g x.

Goal True.
Proof.
  Fail rewrite @equal_f with _ _ _ I 1.
Abort.

Axiom f_eq : forall {P : Type} {p q : P} (f : P -> unit), f p = f q.

Goal False.
Proof.
  Fail rewrite f_eq with (f := tt).
Abort.
