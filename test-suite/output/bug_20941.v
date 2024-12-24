(* Was a unification anomaly in the imitation phase with primitive
   projections (assert false at line 913 of evarsolve.ml) while a regular
   typing error is expected. *)

Set Primitive Projections.
Set Warnings "-notation-overridden".
Notation "x .+1" := (S x) (at level 1, left associativity, format "x .+1").
Notation "x .+2" := (S (S x)) (at level 1, left associativity, format "x .+2").
Notation "x .+3" := (S (S (S x))) (at level 1, left associativity, format "x .+3").
Notation "x .1" := (projT1 x) (at level 1, left associativity, format "x .1").
Notation "x .2" := (projT2 x) (at level 1, left associativity, format "x .2").
Notation "( x ; y )" := (existT _ x y) (at level 0, format "'[' ( x ;  '/ ' y ) ']'").

Inductive leI n: nat -> Type :=
| leI_refl: n <= n
| leI_down p: p.+1 <= n -> p <= n
where "p <= n" := (leI n p): nat_scope.
Arguments leI_down {n p} H.
Lemma leI_raise_both {n p}: p <= n -> p.+1 <= n.+1.
  induction 1. now constructor. now constructor.
Defined.

Class RestrFrameTypeBlock' := {
  RestrFrameType': Type;
  Frame': RestrFrameType' -> Type;
}.

Definition mkRestrFrameTypeBlock' n
  (frame'': forall p (Hp: p.+1 <= n), Type)
  (painting'': forall p (Hp: p.+1 <= n), frame'' p Hp -> Type) :=
  fix aux p: forall (Hp: p <= n), RestrFrameTypeBlock' :=
  match p with
  | O => fun (Hp: 0 <= n) =>
    {| RestrFrameType' := unit; Frame' _ := unit |}
  | S p => fun (Hp: p.+1 <= n) =>
    {|
      RestrFrameType' :=
        { R : (aux p _).(RestrFrameType') &
         (aux p (leI_down Hp)).(Frame') R -> frame'' p Hp };
      Frame' R :=
        { d: (aux p _).(Frame') R.1 & painting'' p Hp (R.2 d) }
    |}
  end.

Class CohFrameTypeBlock n
  (frame'': forall p (Hp: p.+2 <= n), Type)
  (painting'': forall p (Hp: p.+2 <= n), frame'' p Hp -> Type)
  (frame': forall p (Hp: p.+1 <= n), Type) p {Hp: p.+1 <= n} := {
  CohFrameType: Type;
  Frame: forall Q: CohFrameType, Type;
  RestrFrame: forall Q: CohFrameType,
   forall q {Hpq: p.+1 <= q.+1} {Hq: q.+1 <= n},
   Frame Q -> frame' p Hp;
}.

Definition take_head n
  {frame'': forall p {Hp: p.+1 <= n}, Type}
  {painting'': forall p {Hp: p.+1 <= n}, frame'' p -> Type}
  {restrFrames': (mkRestrFrameTypeBlock' n frame'' painting'' n (leI_refl _)).(RestrFrameType')}:
  forall p (Hp: p <= n), (mkRestrFrameTypeBlock' n _ _ p Hp).(RestrFrameType') :=
  fix aux p (Hp: p <= n) :=
  match Hp in p <= _ return (mkRestrFrameTypeBlock' n _ _ p Hp).(RestrFrameType') with
  | leI_refl _ => restrFrames'
  | @leI_down _ p Hp => (aux p.+1 Hp).1
  end.

Definition take_restrFrame' n
  {frame'': forall p {Hp: p.+1 <= n}, Type}
  {painting'': forall p {Hp: p.+1 <= n}, frame'' p -> Type}
  {restrFrames': (mkRestrFrameTypeBlock' n frame'' painting'' n (leI_refl _) ).(RestrFrameType')}
  p (Hp: p.+1 <= n) := (take_head (restrFrames' := restrFrames') n p.+1 Hp).2:
    (mkRestrFrameTypeBlock' n _ _ p (leI_down Hp)).(Frame')
    (take_head (restrFrames' := restrFrames') n p.+1 Hp).1 ->
    frame'' p.

Fail Definition Painting' n p {Hp:p <= n}
  {frame'': forall p {Hp: p.+1 <= n.+1}, Type}
  {painting'': forall p {Hp: p.+1 <= n.+1}, frame'' p -> Type}
  {restrFrames': (mkRestrFrameTypeBlock' n.+1 _ _ n.+1 (leI_refl _)).(RestrFrameType')}
  (frame' := fun p (Hp: p.+1 <= n.+1) =>
    (mkRestrFrameTypeBlock' n.+1 frame'' painting'' p (leI_down Hp)).(Frame')
      (take_head (restrFrames' := restrFrames') n.+1 p (leI_down Hp)))
 (restrFrame' : forall p {Hp:p.+1 <= n.+1} , frame' p Hp-> frame'' p
   := fun p {Hp:p.+1 <= n.+1} => take_restrFrame' (restrFrames' := restrFrames') n.+1 p Hp)
   {E: frame' n (leI_refl _) -> Type}: frame' p (leI_raise_both Hp) -> Type :=
 (fix aux p Hp :=
 match Hp with
  | leI_refl _ => fun _ => E (* this is the typing bug: should be "E" *)
  | @leI_down _ p Hp => fun d =>
       {l: painting'' p (restrFrame' p d) & (aux p.+1 Hp) (d; l)}
  end) p Hp.
