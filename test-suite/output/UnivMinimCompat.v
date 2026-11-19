Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
Set Printing Universes.

Record Box := { carrier : Type }.

Definition box (I : Type) : Box := {| carrier := I |}.

(* The universe of [G] occurs invariantly and is only bounded from below by the universe of [I] *)
Definition same_box (I : Type) (G : Box) (e : G = box I) := e.
About same_box.

Set Universe Minimization Compat.

(* It is identified with the universe of [I] *)
Definition same_box' (I : Type) (G : Box) (e : G = box I) := e.
About same_box'.

(* A universe only bounded from below by [Set] keeps its generality *)
Definition set_box (G : Box) (e : G = box nat) := e.
About set_box.

(* As does one bounded from below by an algebraic universe *)
Definition pair_box (I J : Type) (G : Box) (e : G = box (I * J)) := e.
About pair_box.

(* A universe bounded from above is identified with its lower bound too, when this does not
   constrain the others: [v] with [u], then [w] with [u] *)
Record Chain@{u v w | u <= v, v <= w} := { lo : Type@{u}; mid : Type@{v}; hi : Type@{w} }.
Definition chain (x : Chain) := x.
About chain.

(* As do the universes of the type of a section variable, which are those of the declarations of
   the section *)
Record Cat@{o h p | h <= p} := { ob : Type@{o}; hm : ob -> ob -> Type@{h};
  eqv : forall x y, hm x y -> hm x y -> Type@{p} }.
Section S.
  Context (C : Cat).
  Definition terminal := { t : ob C & forall x, hm C x t }.
End S.
About terminal.
