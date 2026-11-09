Require Import ssreflect ssrbool.

Set Implicit Arguments.
Unset Strict Implicit.

Notation spec lv x := (lv -> (x <> 0)).

Record def (lv : bool) := Def { r :> nat; P : spec lv r }.

Definition from {lv} {x : @def lv} (phx : phantom nat x) := x.

Class unify (x y : bool) := Unify : ~~x.
Hint Extern 0 (unify _ _) => reflexivity : typeclass_instances.

Lemma widen_subproof lv (x : def lv) lv' : unify lv' lv -> spec lv' (r x).
Proof. by case: lv lv' x => [] [] []. Qed.

Definition widen lv (x : def lv) lv' (ulv : unify lv' lv) :=
  Def (@widen_subproof _ x _ ulv).
Arguments widen {lv} _ {_ _}.

Lemma zero_subproof : spec false 0. Proof. by []. Qed.
Canonical zero := Def (zero_subproof).

Lemma test x : x = 0.
Proof.
rewrite -[0]/(r (widen (from (Phantom _ 0)) : def false)).
Fail rewrite -[0]/(r (@Def false 0 _)).
Abort.
