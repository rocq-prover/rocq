From Corelib Require Import ssreflect.
Set Printing Universes.

Definition foo@{i} (A : Type@{i}): nat := let x := Type@{i} in 0.
About foo.

Definition lemma@{i} : foo@{i} nat = 0 := eq_refl.

Lemma test : foo@{0} nat = foo@{1} nat.
Proof.
  rw !lemma. reflexivity.
Qed.

Axiom cheat : forall {A},A.
Lemma test2 : foo@{0} nat = 0 + foo@{1} nat.
Proof.
  rw [X in _ = _ + X]lemma.
  Show Universes.
  cbn.
  apply cheat.

Qed.
