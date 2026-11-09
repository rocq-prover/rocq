Inductive Un : nat -> SProp :=
| an : nat -> Un 1
| bn : nat -> Un 2.

Inductive K : SProp := ak | bk.

Check match an _ with
| an _ => ak
| _ => bk
end.

Definition d1 := match an 0 with an _ => ak | _ => bk end.
Definition d2 (x : Un 1) : K := match x with an _ => ak end.
Definition d3 (n : nat) (x : Un (S n)) : K := match x with an _ => ak | bn _ => bk end.
Definition d4 (x : Un 1) := match x with an _ => ak | _ => bk end.

Inductive Ip : nat -> Prop := ia : Ip 1 | ib : Ip 2.
Definition d5 (x : Ip 1) := match x with ia => ak | _ => bk end.

Inductive J : nat -> Set := ja : J 1 | jb : J 2.

Polymorphic Definition e1@{s;u|} (A : Univ@{s;u}) (a b : A) (x : J 1) : A :=
  match x with ja => a | _ => b end.

(* Without a catch-all branch, the impossible case is given type
   forall A : Univ@{s;u}, A -> A, which lives in Univ@{s;u+1} since
   Univ@{s;u} is not impredicative, so it does not fit in Univ@{s;u}. *)
Fail Polymorphic Definition e2@{s;u|} (A : Univ@{s;u}) (a : A) (x : J 1) : A :=
  match x with ja => a end.
