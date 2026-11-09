Inductive B : nat -> Prop := .
Timeout 10 Fail Inductive C := X : unit_rect _ B tt 0 -> C.
