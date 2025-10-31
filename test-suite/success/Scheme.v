(* This failed in 8.3pl2 *)

Scheme Induction for eq Sort Prop.
Check eq_ind_dep.

(* This was broken in v8.5 *)

Set Rewriting Schemes.
Inductive myeq A (a:A) : A -> Prop := myrefl : myeq A a a.
Unset Rewriting Schemes.

Check myeq_rect.
Check myeq_ind.
Check myeq_rec.
Check myeq_congr.
Check myeq_sym.
Check myeq_rew.
Check myeq_rew_dep.
Check myeq_rew_fwd_dep.
Check myeq_rew_r.
Check myeq_sym_involutive.
Check myeq_rew_r_dep.
Check myeq_rew_fwd_r_dep.

Set Rewriting Schemes.
Inductive myeq_true : bool -> Prop := myrefl_true : myeq_true true.
Unset Rewriting Schemes.

(* check that the scheme doesn't minimize itself into something non general *)
Polymorphic Inductive foo@{u v|u<=v} : Type@{u}:= .
Lemma bla@{u v|u < v} : foo@{u v} -> False.
Proof. induction 1. Qed.

Set Warnings "+deprecated-lookup-elim-by-name".

Unset Elimination Schemes.
Inductive bar := A | B (_:bar).

Scheme bar_myind := Induction for bar Sort Prop.
Scheme bar_myind_nodep := Minimality for bar Sort Prop.

(* ignored *)
Definition bar_ind := bar_myind.

Lemma a_or_b : forall f:bar, f = A \/ exists f', f = B f'.
Proof.
  intros f.
  induction f.
  - left;reflexivity.
  - right;eexists;reflexivity.
Qed.

Fixpoint bar_rec (P : Set) (f : P) (f0 : bar -> P -> P) b :=
  match b with
  | A => f
  | B b0 => f0 b0 (bar_rec P f f0 b0)
  end.

Lemma to_bool : bar -> bool.
Proof.
  intros f.
  Fail induction f.
Abort.

Module Attribute.
  (* test schemes attribute *)

  Set Elimination Schemes.

  #[schemes=none]
    Inductive foo1 := Foo1.
  Fail Check foo1_ind.

  #[schemes=default]
    Inductive foo2 := Foo2.
  Check foo2_ind.

  Unset Elimination Schemes.

  #[schemes=none]
    Inductive foo3 := Foo3.
  Fail Check foo3_ind.

  (* XXX should default ignore Elimination Schemes? *)
  #[schemes=default]
    Inductive foo4 := Foo4.
  Fail Check foo4_ind.

  Set Elimination Schemes.
  Set Rewriting Schemes.

  #[schemes=default]
    Inductive foo5 : bool -> Prop := Foo5 : foo5 true.
  Check foo5_ind.
  Check foo5_rew.

  #[schemes=none]
    Inductive foo6 : bool -> Prop := Foo6 : foo6 true.
  Fail Check foo6_ind.
  Fail Check foo6_rew.

  (* can't do rewriting schemes for this *)
  Fail Inductive foo7 := Foo7.

  (* but disabling schemes doesn't try rewriting schemes *)
  #[schemes=none]
    Inductive foo7 := Foo7.

End Attribute.
