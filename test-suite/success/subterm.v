(** This file tests a few tricky successful cases of commutative
    cuts in the guard condition. *)

Module MutualCut.

Inductive T (A : unit) := node (x : T A) with U (A : unit) := .

Axiom e : tt = tt.

(** Commutative cut returning a non-trivial mutual. *)
Fixpoint F (x : T tt) : False :=
  match x with
  | node _ x =>
    F match e in _ = t return T t with eq_refl => x end
  end.

End MutualCut.

Module NestedCut.

Set Warnings "-register-all".

Inductive T := node : prod (list T) (list T) -> T.

Axiom e : T = T.

(** This succeeds because the size of the second projection is unchanged by the cast *)
Fixpoint F (t : T) : unit := match t with
| node p =>
  let p := match e in _ = X return prod (list X) (list T) with eq_refl => p end in
  let l := snd p in
  match l with
  | nil => tt
  | cons x _ => F x
  end
end.

(** This fails because the size of the first projection is destroyed by the cast *)
Fail Fixpoint G (t : T) : unit := match t with
| node p =>
  let p := match e in _ = X return prod (list X) (list T) with eq_refl => p end in
  let l := fst p in
  match l with
  | nil => tt
  | cons x _ => G x
  end
end.

End NestedCut.
