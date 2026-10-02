(* Scala 3 extraction backend (plugins/extraction/scala.ml): the basic,
   monomorphic case - a self-recursive [Dfix] whose real, stored type
   lets [typed_signature] give it a genuine Scala signature instead of
   the uniform [Any] fallback, and whose body needs the whole-body
   [asInstanceOf] cast documented in SCALA_EXTRACTION.md ("The
   exception: real top-level signatures"). *)

Require Import Extraction.

Extraction Language Scala.

Fixpoint addNat (n m : nat) : nat :=
  match n with
  | 0 => m
  | S p => S (addNat p m)
  end.

Fixpoint mulNat (n m : nat) : nat :=
  match n with
  | 0 => 0
  | S p => addNat m (mulNat p m)
  end.

Recursive Extraction addNat mulNat.
