(* A projection of a class on an evar, to be solved by typeclass resolution:
   the class has no canonical instance and the record is not looked for by
   unfolding the other side, which would pick [isgraph_G] for
   [IsGraph (op G)] below. *)
Set Primitive Projections.

Class IsGraph (A : Type) := { Hom : A -> A -> Type }.

Definition op (A : Type) := A.
#[global] Typeclasses Opaque op.

#[export] Instance isgraph_op (A : Type) {H : IsGraph A} : IsGraph (op A) :=
  {| Hom := fun a b : A => @Hom A H b a |}.

Parameter G AG : Type.
Parameter g_of : AG -> G.
Coercion g_of : AG >-> G.
Parameter homG : G -> G -> Type.
#[export] Instance isgraph_G : IsGraph G := {| Hom := homG |}.
#[export] Instance isgraph_AG : IsGraph AG := {| Hom := fun a b : AG => @Hom G isgraph_G a b |}.

Parameter fmap : forall (A : Type) {H : IsGraph A} (a b : A), @Hom A H a b -> Type.
Arguments fmap A {H a b} f.

Definition test (a b : AG) (f : Hom a b) := fmap (op G) f.

Goal forall (a b : AG) (f : Hom a b),
  test a b f = @fmap (op G) (isgraph_op G) (g_of b) (g_of a) f.
Proof. intros; reflexivity. Qed.
