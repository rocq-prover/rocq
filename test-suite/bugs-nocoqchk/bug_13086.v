Unset Universe Checking.

Definition bad1@{|Set < Set} := Prop.

Set Universe Polymorphism.
Axiom ax : Type.
Inductive I@{u} : Prop := foo : ax@{u} -> I.

Definition bad2@{v} (x:I@{v}) : I@{Set} := x.
Set Debug "backtrace".
Definition vsdvds (f : (Prop -> Prop) -> Prop) (x : Set -> Prop) := f x.
