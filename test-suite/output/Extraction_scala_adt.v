(* Scala 3 extraction backend: a multi-field self-recursive constructor
   ([tree]'s [Node], with two recursive fields sharing the inductive's
   own type parameter) and a simple sum type ([myOption]) - exercises
   the constructor-field-cast machinery in SCALA_EXTRACTION.md
   ("Constructor fields", [discover_field_instantiation]). *)

Require Import Extraction.

Extraction Language Scala.

Fixpoint addNat (n m : nat) : nat :=
  match n with
  | 0 => m
  | S p => S (addNat p m)
  end.

Inductive tree (A : Type) : Type :=
  | Leaf : tree A
  | Node : tree A -> A -> tree A -> tree A.

Arguments Leaf {A}.
Arguments Node {A} _ _ _.

Fixpoint treeSum (t : tree nat) : nat :=
  match t with
  | Leaf => 0
  | Node l x r => addNat (treeSum l) (addNat x (treeSum r))
  end.

Fixpoint treeMap (A B : Type) (f : A -> B) (t : tree A) : tree B :=
  match t with
  | Leaf => Leaf
  | Node l x r => Node (treeMap A B f l) (f x) (treeMap A B f r)
  end.

Inductive myOption (A : Type) : Type :=
  | MyNone : myOption A
  | MySome : A -> myOption A.

Arguments MyNone {A}.
Arguments MySome {A} _.

Definition optionMap (A B : Type) (f : A -> B) (o : myOption A) : myOption B :=
  match o with
  | MyNone => MyNone
  | MySome a => MySome (f a)
  end.

Recursive Extraction treeSum treeMap optionMap.
