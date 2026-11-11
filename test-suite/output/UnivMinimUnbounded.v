Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
Set Printing Universes.

Record Box := { carrier : Type }.

Definition box (I : Type) : Box := {| carrier := I |}.

(* The universe of [G] occurs invariantly and is only bounded from below by the universe of [I] *)
Definition same_box (I : Type) (G : Box) (e : G = box I) := e.
About same_box.

Set Universe Minimization Unbounded.

(* It is identified with the universe of [I] *)
Definition same_box' (I : Type) (G : Box) (e : G = box I) := e.
About same_box'.

(* A universe only bounded from below by [Set] keeps its generality *)
Definition set_box (G : Box) (e : G = box nat) := e.
About set_box.

(* As does one bounded from below by an algebraic universe *)
Definition pair_box (I J : Type) (G : Box) (e : G = box (I * J)) := e.
About pair_box.
