(* The universes in the binders of a toplevel fixpoint are not irrelevant for conversion,
   even when the constant is fully applied: a stuck unfolded fixpoint keeps its binders, and
   conversion compares them with the unfolding of another instance *)

Set Universe Polymorphism.
Inductive seq@{u} (T : Type@{u}) : Type@{u} := nil | cons (x : T) (xs : seq T).
Arguments nil {T}. Arguments cons {T}.
Fixpoint size@{u} {T : Type@{u}} (xs : seq@{u} T) : nat :=
  match xs with nil => 0 | cons _ xs => S (size xs) end.
Unset Universe Polymorphism.

Universes a b.
Constraint a < b.

(* Without the fix, this was accepted with no constraint, while the kernel needs a = b as soon as
   one side is unfolded *)
Fail Definition t1 (T : Type@{a}) (xs : seq@{a} T) : size@{a} xs = size@{b} xs := eq_refl.

Fail Definition t2 (T : Type@{a}) (x : T) (xs : seq@{a} T) :
  size@{a} (cons x xs) = S (size@{b} xs) := eq_refl.

Definition t3@{c} (T : Type@{a}) (x : T) (xs : seq@{a} T) :
  size@{a} (cons x xs) = S (size@{c} xs) := eq_refl.
