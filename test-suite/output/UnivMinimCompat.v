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

(* A universe occurring in the type is not set to Set, even when the inference reduces it away:
   the type, unreduced, would make Set reach the definitions unifying with it *)
Record Q@{a} := { nodes : Type@{a} }.
Definition q@{a} : Q@{a} := {| nodes := nat |}.
Definition f (x : nodes q) := x.
About f.

(* The universes of the body only weakly related to those of the type, here by a conversion of
   [gcar (free A)] up to reduction, are identified with them rather than set to Set: the body,
   unfolded, would make Set reach the universes of the type *)
Unset Universe Minimization ToSet.
Record G@{a e} := { gcar : Type@{a}; grel : gcar -> gcar -> Type@{e} }.
Definition free@{a} (A : Type@{a}) : G@{a 0} := {| gcar := list A; grel := fun _ _ => True |}.
Definition gop (g : G) (x y : gcar g) : gcar g := x.
Definition ins (A : Type) (a : A) : gcar (free A) := cons a nil.
Definition w (A : Type) (a : A) : gcar (free A) := gop (free A) (ins A a) (ins A a).
Print w.

(* Also when the universes of the type are algebraic, e.g. [l := max(u, u0, u1)] in the type of
   [pl], jointly: [glue@{a b}] with [a ~ l], [b ~ l], where [b] is bounded by the universe of
   [B + C], itself only weakly related to the universes of [B] and [C] *)
Inductive Co@{i j u | i <= u, j <= u} (B : Type@{i}) (A : Type@{j}) (f : B -> A) : Type@{u} :=
  co : A -> Co B A f.
Arguments co {B A f} _.
Axiom glue@{i j} : forall (B : Type@{i}) (A : Type@{j}) (f : B -> A) (b : B),
  @co B A f (f b) = @co B A f (f b).
Definition Po@{i j k l} (A : Type@{i}) (B : Type@{j}) (C : Type@{k}) (f : A -> B) : Type@{l}
  := Co@{l l l} A (B + C) (fun a => inl (f a)).
Definition pl (A B C : Type) (f : A -> B) (b : B) : Po A B C f :=
  @co A (B + C) (fun a => inl (f a)) (inl b).
Definition pg (A B C : Type) (f : A -> B) (a : A) : pl A B C f (f a) = pl A B C f (f a)
  := glue A (B + C) (fun a => inl (f a)) a.
Print pg.

(* As for the type of a definition, a universe occurring in the type of a section variable, even
   when the inference reduces it away, is not set to Set *)
Section Var.
  Context (x : nodes q).
  Definition fx := x.
End Var.
About fx.
