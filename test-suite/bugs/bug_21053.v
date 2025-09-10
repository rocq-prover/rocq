Notation "'rew' [ f ] e 'in' x" := (eq_rect _ f x _ e) (at level 10, x at level 10).

Definition cast {A B : Set} (e : A = B) : A -> B :=
  rew [fun (T : Set) => T -> B] eq_sym e in fun x => x.

Definition castP {A B : Prop} (e : A = B) : A -> B :=
  rew [fun T => T -> B] eq_sym e in fun x => x.


Inductive True2 : Prop := I2 : (False -> True2) -> True2.

Fail Fixpoint f (e : (False -> True2) = True2) (x : True2) {struct x} : False :=
  match x with
  | I2 H => f e (castP e H)
  end.
(* Problematic fixpoint : [castP e f] should not be a subterm of [f] *)

#[bypass_check(guard)]
Fixpoint f (e : (False -> True2) = True2) (x : True2) {struct x} : False :=
  match x with
  | I2 H => f e (castP e H)
  end.

Section contradiction.
Context (prop_ext: forall P Q, (P <-> Q) -> P = Q).

Theorem e : (False -> True2) = True2.
Proof.
  apply prop_ext. split; auto using I2.
Qed.

Definition contradiction := f e (I2 (False_rect True2)).
End contradiction.



Fail Fixpoint g (e : nat = nat) (n : nat) {struct n} :=
  match n with
  | 0 => 0
  | S n => S (g e (cast e n))
end.
(* Problematic fixpoint : [cast e n] should not be a subterm of [n] *)

#[bypass_check(guard)]
Fixpoint g (e : nat = nat) (n : nat) {struct n} :=
  match n with
  | 0 => 0
  | S n => S (g e (cast e n))
end.

Section Issue.
Context (e : nat = nat). (* Supposed non-trivial *)
Context (e0 : rew [fun (T : Set) => T] e in 0 = 1).
(* How the non triviality may appear *)

Corollary e0' : cast e 0 = 1.
Proof.
  rewrite <- e0. clear e0.
  unfold cast.
  generalize 0.
  destruct e.
  reflexivity.
Defined.

Theorem Boom : False.
  enough (g e 1 = S (g e 1)) by now induction (g e 1); auto.
  change (g e 1) with (S (g e (cast e 0))) at 1.
  f_equal. f_equal.
  apply e0'.
Qed.

End Issue.
