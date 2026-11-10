Inductive A (n : nat) := .
Inductive B {n : nat} : A n -> A n -> Prop := .
Timeout 10 Fail Inductive C : A 0 -> Type := X a : unit_rect _ B tt a a -> C a.
