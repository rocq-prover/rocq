(* Scala 3 extraction backend: genuine mutual (non-self) recursion
   between two [Dfix] members of one block ([isEven]/[isOdd]) - which
   does *not* get the explicit-type-argument treatment reserved for
   *self*-recursive calls (see SCALA_EXTRACTION.md,
   "Self-relativity..."); and a custom-extracted inductive ([bool],
   via [Extract Inductive]), whose constructor is a bare, non-applied
   literal rather than a case class. *)

Require Import Extraction.

Extraction Language Scala.

Fixpoint isEven (n : nat) : bool :=
  match n with
  | 0 => true
  | S p => isOdd p
  end
with isOdd (n : nat) : bool :=
  match n with
  | 0 => false
  | S p => isEven p
  end.

Extract Inductive bool => "Boolean" [ "true" "false" ].

Definition myNot (b : bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Recursive Extraction isEven isOdd myNot.
