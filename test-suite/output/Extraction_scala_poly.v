(* Scala 3 extraction backend: polymorphic, self-recursive functions
   whose curried parameters share an inductive type variable
   ([myMap]'s/[myFold]'s own [A]/[B] in both a higher-order parameter
   and the list argument) - the [pinned_real]/[pinned_any] tracking and
   the explicit-type-argument treatment of self-relative calls in
   SCALA_EXTRACTION.md ("Self-relativity and the pinned-variable
   problem", "Reducing casts on applications"). [emptyList] is a
   zero-argument polymorphic [Dterm], printed as a parameterized [def]
   since Scala's [val] cannot itself carry a type parameter. *)

Require Import Extraction.

Extraction Language Scala.

Inductive myList (A : Type) : Type :=
  | MyNil : myList A
  | MyCons : A -> myList A -> myList A.

Arguments MyNil {A}.
Arguments MyCons {A} _ _.

Fixpoint myLength (A : Type) (l : myList A) : nat :=
  match l with
  | MyNil => 0
  | MyCons _ t => S (myLength A t)
  end.

Fixpoint myMap (A B : Type) (f : A -> B) (l : myList A) : myList B :=
  match l with
  | MyNil => MyNil
  | MyCons a t => MyCons (f a) (myMap A B f t)
  end.

Fixpoint myAppend (A : Type) (l1 l2 : myList A) : myList A :=
  match l1 with
  | MyNil => l2
  | MyCons a t => MyCons a (myAppend A t l2)
  end.

(* Accumulator-first argument order: a different curried-parameter shape
   than [myMap]/[myAppend]'s own, still self-recursive and still sharing
   a type variable ([A]) between a higher-order parameter and the
   list. *)
Fixpoint myFold (A B : Type) (f : B -> A -> B) (acc : B) (l : myList A) : B :=
  match l with
  | MyNil => acc
  | MyCons a t => myFold A B f (f acc a) t
  end.

(* A match nested inside a match, and a self-recursive call whose shared
   type variable is *not* the same as the list's own head element in the
   surrounding scope ([bool] vs [A]). *)
Fixpoint myAll (A : Type) (f : A -> bool) (l : myList A) : bool :=
  match l with
  | MyNil => true
  | MyCons a t =>
    match f a with
    | true => myAll A f t
    | false => false
    end
  end.

Definition compose (A B C : Type) (f : B -> C) (g : A -> B) (x : A) : C := f (g x).

Definition emptyList (A : Type) : myList A := MyNil.

Recursive Extraction myLength myMap myAppend myFold myAll compose emptyList.
