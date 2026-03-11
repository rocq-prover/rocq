From Corelib Require Import PrimArray.

Set Universe Polymorphism.

Local Abbreviation in_bounds i t := (PrimInt63.ltb i (length t)).

Axiom get_out_of_bounds@{u} : forall (A:Type@{u}) (t:array A) i,
  in_bounds i t = false -> t.[i] = default t.

Axiom get_set_same@{u} : forall (A:Type@{u}) t i (a:A),
  in_bounds i t = true -> t.[i<-a].[i] = a.
Axiom get_set_other@{u} : forall (A:Type@{u}) t i j (a:A), i <> j -> t.[i<-a].[j] = t.[j].
Axiom default_set@{u} : forall (A:Type@{u}) t i (a:A), default t.[i<-a] = default t.


Axiom get_make@{u} : forall (A:Type@{u}) (a:A) size i, (make size a).[i] = a.

Axiom leb_length@{u} : forall (A:Type@{u}) (t:array A),
  PrimInt63.leb (length t) max_length = true.

Axiom length_make@{u} : forall (A:Type@{u}) size (a:A),
  length (make size a) = if PrimInt63.leb size max_length then size else max_length.
Axiom length_set@{u} : forall (A:Type@{u}) t i (a:A),
  length t.[i<-a] = length t.

Axiom get_copy@{u} : forall (A:Type@{u}) (t:array A) i, (copy t).[i] = t.[i].
Axiom length_copy@{u} : forall (A:Type@{u}) (t:array A), length (copy t) = length t.

Axiom array_ext@{u} : forall (A:Type@{u}) (t1 t2:array A),
  length t1 = length t2 ->
  (forall i, in_bounds i t1 = true -> t1.[i] = t2.[i]) ->
  default t1 = default t2 ->
  t1 = t2.
