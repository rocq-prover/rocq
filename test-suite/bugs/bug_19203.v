Set Universe Polymorphism.

Inductive bool@{q; |} : Type@{q;Set} := | true : bool | false : bool.

Definition nand@{q; |} (a b : bool@{q;}) : bool@{q;} :=
  match a , b with
  | true , true => false
  | _ , _ => true
  end.

Inductive seq@{q;u|} {A : Type@{q;u}} (a : A) : A -> Type@{q;u} := | srefl : seq a a.
Arguments srefl {_ _}.

#[universes(polymorphic=yes)]
Instance seq_Has_Leibniz_elim@{s; l l' l''} : Has_Leibniz@{s s s;l l' l''} (@seq) :=
  fun A x P t y e => match e with srefl => t end.

Register seq as core.eq.type.
Register srefl as core.eq.refl.

Lemma foo@{q; |} (f : bool@{q;} -> bool@{q;}) (x : bool@{q;}) : seq (f true) (f true).
Proof.
  remember (f true) as b eqn : ftrue.
  reflexivity.
Qed.

Lemma f3_eq_f@{q; |} (f : bool@{q;} -> bool@{q;}) (x : bool@{q;}) : seq (f (f (f x))) (f x).
Proof.
  remember (f true) as b eqn : ftrue.

  remember (f false) as c eqn : ffalse.
  Validate Proof.

  destruct x,b,c.
  all:repeat rewrite <-?ftrue, <-?ffalse.
  all: reflexivity.
Qed.
