From Corelib Require Import PrimInt63.

Set Universe Polymorphism.

Primitive array@{u} : Type@{u} -> Type@{u} := #array_type.

Primitive make@{u}: forall A : Type@{u}, int -> A -> array A := #array_make.
Arguments make {_} _ _.

Primitive get@{=u} : forall A : Type@{u}, array A -> int -> A := #array_get.
Arguments get {_} _ _.

Primitive default@{u} : forall A : Type@{u}, array A -> A:= #array_default.
Arguments default {_} _.

Primitive set@{u} : forall A : Type@{u}, array A -> int -> A -> array A := #array_set.
Arguments set {_} _ _ _.

Primitive length@{u} : forall A : Type@{u}, array A -> int := #array_length.
Arguments length {_} _.

Primitive copy@{u} : forall A : Type@{u}, array A -> array A := #array_copy.
Arguments copy {_} _.

Module Export PArrayNotations.

Declare Scope array_scope.
Delimit Scope array_scope with array.
Notation "t .[ i ]" := (get t i)
  (at level 2, left associativity, format "t .[ i ]").
Notation "t .[ i <- a ]" := (set t i a)
  (at level 2, left associativity, format "t .[ i <- a ]").

End PArrayNotations.

Primitive max_length := #array_max_length.
