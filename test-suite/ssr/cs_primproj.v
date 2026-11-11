From Corelib Require Import ssreflect.

(* Matching a pattern headed by a canonical projection against values which
   are primitive projections *)

Set Primitive Projections.
Record additive := Additive { afun :> nat -> nat; afun0 : afun 0 = 0 }.
Record law := Law { lop :> nat -> nat -> nat; lop0 : forall a, lop a 0 = 0 }.
Unset Primitive Projections.

Lemma add0 (f : additive) : f 0 = 0.
Proof. by case: f. Qed.

Lemma law0 (s : law) a : s a 0 = 0.
Proof. by case: s. Qed.

(* The key of this instance is the primitive projection [lop] with an
   argument besides the record *)
Canonical law_additive (s : law) a := Additive (s a) (law0 s a).

Lemma test (s : law) a : s a 0 = 0.
Proof. by rewrite add0. Qed.

Lemma test_pattern (s : law) a b : s a 0 + s b 0 = 0.
Proof. by rewrite [in X in _ + X]add0 add0. Qed.

(* The same value as the application of the compatibility constant of the
   projection *)
Lemma test_constant (s : law) a :
  ltac:(let c := eval cbv beta in ((fun f : law -> nat -> nat -> nat => f s a 0) lop) in
        exact (c = 0)).
Proof. by rewrite add0. Qed.
