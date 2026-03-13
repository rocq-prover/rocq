Set Universe Polymorphism.
Inductive Box@{s; u} (A : Type@{u}) : Type@{s; u} := box (x : A).

Module Type M.
  Parameter T@{s; u} : forall A, Box@{s; u} A -> Box@{Type; u} A.
  Parameter T_correct@{s; u} : forall (A : Type@{u}) x, T@{s; u} A (box@{s; u} _ x) = box@{Type; u} _ x.
End M.

Module M2.
  Definition T@{s; u|s -> Type} := fun A (x : Box@{s; u} A) => match x with box _ y => box@{Type;u} _ y end.
  Definition T_correct@{s; u|s -> Type} : forall (A : Type@{u}) x, T@{s; u} A (box@{s; u} _ x) = box@{Type; u} _ x := fun A x => eq_refl.
End M2.

Fail Module M3 : M := M2.

Unset Universe Polymorphism.
Inductive squash (A : Type) : SProp := sq (x : A).
Fail Definition unbox A (x : squash A) : A :=
  match M2.T A (match x return Box@{SProp; _} _ with sq _ y => box _ y end) with box _ y => y end.
