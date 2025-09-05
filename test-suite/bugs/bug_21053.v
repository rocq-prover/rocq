Notation "'rew' [ f ] e 'in' x" := (eq_rect _ f x _ e) (at level 10, x at level 10).

Definition cast_rev e : nat -> nat :=
  rew [fun (T : Set) => T -> nat] eq_sym e in fun x => x.

Fail Fixpoint f (e : nat = nat) (n : nat) {struct n} :=
  match n with
  | 0 => 0
  | S n => S (f e (cast_rev e n))
end.
(* Problematic fixpoint : [cast_rev_e n] should not be a subterm of [n] *)

#[bypass_check(guard)]
Fixpoint f (e : nat = nat) (n : nat) {struct n} :=
  match n with
  | 0 => 0
  | S n => S (f e (cast_rev e n))
end.

Section Issue.
Context (e : nat = nat). (* Supposed non-trivial *)
Context (e0 : rew [fun (T : Set) => T] e in 0 = 1).
(* How the non triviality may appear *)

Corollary e0' : cast_rev e 0 = 1.
Proof.
  rewrite <- e0. clear e0.
  unfold cast_rev.
  generalize 0.
  destruct e.
  reflexivity.
Defined.

Theorem Boom : False.
  enough (f e 1 = S (f e 1)) by now induction (f e 1); auto.
  change (f e 1) with (S (f e (cast_rev e 0))) at 1.
  f_equal. f_equal.
  apply e0'.
Qed.

End Issue.
