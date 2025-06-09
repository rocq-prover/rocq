Require Extraction.

Set Universe Polymorphism.
Definition foo@{s; |} := tt.

Definition bar := foo@{Prop;}.

Extraction bar.

(* the actual problem only appears once we have inductives with sort poly output: *)

Inductive Pair@{s;u|} (A:Type@{s;u}) : Type@{s;u} := pair : A -> A -> Pair A.

Definition use_pair@{s;+|} A (k:A->nat) (x:Pair@{s;_} A) :=
  k (match x with pair _ x _ => x end).

Definition make_pair := pair@{Prop;_} _ I I.

Definition hell := use_pair True (fun _ => 0) make_pair.

Extraction TestCompile hell.

(* Some tests *)

Module Foo.

Definition foo@{s1 s2| |} := fun (A : Type@{s1|Set}) (x : A) => x.

Definition foo0 := foo@{SProp Type|}.
Definition foo1 := foo@{Type SProp|}.

Inductive T@{s| |} : Type@{s|Set} := O : T | S : T -> T.

Inductive box@{s1 s2| |} (A : Type@{s1|Set}) (B : Type@{s2|Set}) : Type@{Set} := Box : A -> B -> box A B.

Definition bar (A : Type) (x : A) := 0.

Definition qux := bar (forall A : Prop, A -> A) foo@{Prop Type|}.

End Foo.

Extraction TestCompile Foo.

(* Check module subtyping *)

Module Type S.
Inductive box@{s1 s2| |} (A : Type@{s1|Set}) (B : Type@{s2|Set}) : Type@{Set} := Box : A -> B -> box A B.
End S.

Module Bar : S.
Inductive box@{s1 s2| |} (A : Type@{s1|Set}) (B : Type@{s2|Set}) : Type@{Set} := Box : A -> B -> box A B.
End Bar.

Extraction TestCompile Bar.
