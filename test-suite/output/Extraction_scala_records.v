(* Scala 3 extraction backend: records - a monomorphic record printed
   as a single named-field case class ([point]), read back via the
   record-field-projection printing in SCALA_EXTRACTION.md ("Record
   field projection", [pp_record_proj]/[record_proj_shape]); and a
   polymorphic record with a single field, which extraction erases to a
   bare type alias ([Singleton] inductive, [box]/[mapBox]). *)

Require Import Extraction.

Extraction Language Scala.

Record point : Type := MkPoint { px : nat ; py : nat }.

Definition swap (p : point) : point := MkPoint (py p) (px p).

Record box (A : Type) : Type := MkBox { unbox : A }.

Arguments MkBox {A} _.
Arguments unbox {A} _.

Definition mapBox (A B : Type) (f : A -> B) (b : box A) : box B :=
  MkBox (f (unbox b)).

Recursive Extraction swap mapBox.
