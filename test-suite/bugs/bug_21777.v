Set Universe Polymorphism.
Cumulative Inductive foo@{u} : Type@{u} := .

Unset Universe Polymorphism.
Universes u v.
Constraint u < v.

Type eq_refl foo : foo@{u} = foo@{v}.
(* succeeds *)

Type eq_refl foo <: foo@{u} = foo@{v}.
(* fails *)

Type eq_refl foo <<: foo@{u} = foo@{v}.
(* fails *)

Polymorphic Cumulative Inductive bar@{u} := B (_:Type@{u}).

Definition cast@{u v|u < v} (x:bar@{u}) := (x : bar@{v}).
Definition vmcast@{u v|u < v} (x:bar@{u}) := (x <: bar@{v}).

(* fix #21808 to stop failing *)
Fail Definition nativecast@{u v|u < v} (x:bar@{u}) := (x <<: bar@{v}).
