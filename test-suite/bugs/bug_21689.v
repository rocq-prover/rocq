Set Universe Polymorphism.
Definition X@{u} := nat.
Cumulative Inductive bla@{u} : let x := X@{u} in x -> Prop := .

Definition bli@{a b} A (b:bla@{b} A)
  := eq_refl : match b in bla x y return y=y with end = match b in bla x y return id y=y with end.
(* Error: Anomaly "Uncaught exception Invalid_argument("index out of bounds")." *)
