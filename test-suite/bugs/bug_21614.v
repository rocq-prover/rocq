Inductive test : Type := test_intro : (exists x : nat, True) -> test.

Lemma test_lemma (x y : nat) :
test_intro (ex_intro _ x I) = test_intro (ex_intro _ y I) ->
    (ex_intro _ x I) = (ex_intro _ y I).
Proof.
  intros [=].
Abort.

Inductive squash A : Prop := sq (x : A).

Goal sq _ true = sq _ false -> False.
Proof.
  intros [=].
Abort.

Set Keep Proof Equalities.

Lemma test_lemma x y :
test_intro x = test_intro y -> x = y.
Proof.
  intros [=]. assumption.
Abort.
