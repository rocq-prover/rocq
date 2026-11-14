Module HoTT.

Unset Elimination Schemes.

Inductive Circle := base.
Axiom loop : base = base.

Definition Circle_rec (P : Type) (b : P) (l : b = b) (x : Circle) : P :=
  match x with base => b end.

Definition ap {A B} (f : A -> B) {x y} (p : x = y) : f x = f y :=
  match p with eq_refl => eq_refl end.

Axiom Circle_rec_beta_loop : forall P b l, ap (Circle_rec P b l) loop = l.

Definition apD10 {A B} {f g : forall x : A, B x} (p : f = g) : forall x, f x = g x :=
  fun x => match p with eq_refl => eq_refl end.

Check fun x => apD10 (ap _ (Circle_rec_beta_loop _ _ _)) x.

End HoTT.

Module UniMath.

Set Primitive Projections.
Set Implicit Arguments.
Record total2 {A : Type} (P : A -> Type) := tpair { pr1 : A; pr2 : P pr1 }.
Arguments tpair {_} _ _ _.

Definition maponpaths {A B} (f : A -> B) {x y : A} (p : x = y) : f x = f y :=
  match p with eq_refl => eq_refl end.

Record cat := { ob :> Type }.
Definition functor (C D : cat) := total2 (fun f : C -> D => unit).
Definition fob {C D} (F : functor C D) : C -> D := pr1 F.
Coercion fob : functor >-> Funclass.

Definition iso {C : cat} (a b : C) := total2 (fun f : a = b => unit).
Parameter idtoiso : forall {C : cat} {a b : C}, a = b -> iso a b.

Parameter equalizer : forall {C D : cat} (F G : functor C D), cat.
Axiom equalizer_ob : forall {C D : cat} (F G : functor C D),
  ob (equalizer F G) = total2 (fun x : C => F x = G x).

Definition eq_ob {C D} {F G : functor C D} : equalizer F G -> total2 (fun x : C => F x = G x) :=
  fun x => match equalizer_ob F G in _ = T return T with eq_refl => x end.

Goal forall (C1 C2 C0 : cat) (F G : functor C1 C2) (K L : functor C0 (equalizer F G)) (x : C0)
  (e : eq_ob (K x) = eq_ob (L x)) (q : pr1 (eq_ob (K x)) = pr1 (eq_ob (L x))),
  pr1 (idtoiso (maponpaths (@pr1 _ _) e)) = pr1 (idtoiso q).
Proof.
intros.
apply (maponpaths (fun x => _ (idtoiso x))).
Abort.

End UniMath.
