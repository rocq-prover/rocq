(* Scala 3 extraction backend: coinductive types, monomorphic and
   polymorphic - the [RocqLazy] wrapper and forcing/cast machinery in
   SCALA_EXTRACTION.md ("Coinductive types"). [takeList] additionally
   exercises the coinductive "unsafe skolem" cast-fallback alongside a
   self-recursive call that also shares a type variable with the
   coinductive scrutinee. *)

Require Import Extraction.

Extraction Language Scala.

Inductive myList (A : Type) : Type :=
  | MyNil : myList A
  | MyCons : A -> myList A -> myList A.

Arguments MyNil {A}.
Arguments MyCons {A} _ _.

CoInductive stream (A : Type) : Type :=
  | Scons : A -> stream A -> stream A.

Arguments Scons {A} _ _.

CoFixpoint const_stream (n : nat) : stream nat := Scons n (const_stream n).

CoFixpoint mapStream (A B : Type) (f : A -> B) (s : stream A) : stream B :=
  match s with
  | Scons a t => Scons (f a) (mapStream A B f t)
  end.

Fixpoint take (n : nat) (s : stream nat) : list nat :=
  match n with
  | 0 => nil
  | S p =>
    match s with
    | Scons h t => cons h (take p t)
    end
  end.

Fixpoint takeList (A : Type) (n : nat) (s : stream A) : myList A :=
  match n with
  | 0 => MyNil
  | S p =>
    match s with
    | Scons a t => MyCons a (takeList A p t)
    end
  end.

Recursive Extraction const_stream mapStream take takeList.
