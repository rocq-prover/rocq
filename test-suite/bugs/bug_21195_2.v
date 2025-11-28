(* It should be possible to define this *)
Polymorphic Inductive Foo@{s ; u | Prop -> s, Set < u} (A : Type@{s;u}) : Prop := foo : A -> Foo A.
