Set Universe Polymorphism.

Inductive Acc@{s s';u v} {A : Type@{s;u}} (R : A -> A -> Prop) (x : A) : Type@{s';v} :=
| Acc_intro : (forall y : A, R y x -> Acc R y) -> Acc R x.

(* We should be able to define a fixpoint from [s'] to [Type] if [s' -> Prop]. *)
Fixpoint Acc_elim'@{s s' ; u v w | s' -> Prop, u <= w}
  {A : Type@{s;u}} {R : A -> A -> Prop} {P : A -> Type@{w}}
  (f : forall x : A, (forall y : A, R y x -> Acc@{s s';u w} R y) -> (forall y : A, R y x -> P y) -> P x)
  (x : A) (a : Acc@{s s';u w} R x) {struct a} : P x :=
  f x (fun y r => match a with Acc_intro _ _ a0 => a0 y r end)
    (fun y r => Acc_elim' f y (match a with Acc_intro _ _ a0 => a0 y r end)).

(* In fact, we should be able to define a fixpoint from [s''] to any [s'] if [s'' -> Prop]. *)
Fixpoint Acc_elim@{s s' s'' ; u v w | s'' -> Prop, u <= w}
  {A : Type@{s;u}} {R : A -> A -> Prop} {P : A -> Type@{s';v}}
  (f : forall x : A, (forall y : A, R y x -> Acc@{s s'';u w} R y) -> (forall y : A, R y x -> P y) -> P x)
  (x : A) (a : Acc@{s s'';u w} R x) {struct a} : P x :=
  f x (fun y r => match a with Acc_intro _ _ a0 => a0 y r end)
    (fun y r => Acc_elim f y (match a with Acc_intro _ _ a0 => a0 y r end)).
