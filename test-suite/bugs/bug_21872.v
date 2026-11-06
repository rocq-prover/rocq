Set Definitional UIP.
Module Export IsomorphismDefinitions.
#[export]
Set Universe Polymorphism.
Inductive eq@{s;u} {α:Univ@{s;u}} (a:α) : α -> SProp
:= eq_refl : eq a a.
Arguments eq_rect [α] a P _ y _ : rename.
Section Bug.
Variable (A : Type) (f : A -> A).
Variable (hf : forall x, IsomorphismDefinitions.eq (f x) x).
Variable (P : A -> Type).
Variable (a : A) (H : P (f a)).
Fail Definition bug : P a :=
IsomorphismDefinitions.eq_rect _ _ (fun x _ => P x) H _ (hf a).
End Bug.
End IsomorphismDefinitions.
