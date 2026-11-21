(* Conversion compares two stuck matches with CONV (their return clauses and their branches):
   the variance inference must not let cumulativity go through matches. *)

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Definition stype_of@{u v | v < u} (b : bool) : Type@{u} :=
  match b with true => Type@{v} | false => Prop end.

Definition selem_of@{i j} {b : bool} : stype_of@{i j} b -> Type@{j} :=
  match b return stype_of b -> Type@{j} with
  | true => fun x => x | false => fun x => x end.

(* The universe of the branch is invariant, as when the match is unfolded *)
Fail Definition stype_of_cumul@{u v v' | v < u, v' < u, v < v'} (b : bool)
  (S : stype_of@{u v} b) : stype_of@{u v'} b := S.

Definition W (b : bool) := stype_of b.

(* Elaboration used to compare the two stype_of heads after unfolding W, covariantly in the
   universe of the branch, while the kernel unfolds stype_of first and compares the matches
   invariantly: the kernel rejected the elaborated fixpoint. *)
Fixpoint f {b : bool} (n : nat) : W b -> Type :=
  match n return W b -> _ with
  | 0 => fun S => selem_of S
  | Datatypes.S n => fun S => forall x : Type, f n S
  end.

(* The return clause of a stuck match with inversion (on an SProp inductive) has its
   universes inferred: h@{a} and h@{b} are not convertible, as their unfoldings are not. *)
Set Definitional UIP.

Inductive sEq {A : Type} (a : A) : A -> SProp := srefl : sEq a a.

(* The return clause depends on the index, so that the match does not reduce *)
Definition h@{u} (x y : nat) (e : sEq x y) : y = x -> Type@{u} :=
  match e in sEq _ z return z = x -> Type@{u} with srefl _ => fun _ => nat end.

Fail Definition h_irrelevant@{a b | a < b} x y (e : sEq x y)
  : @eq (y = x -> Type@{b}) (h@{a} x y e) (h@{b} x y e) := eq_refl.
