(* -*- mode: coq; coq-prog-args: ("-accessible-goal-names") -*- *)

Goal forall a b : bool, a = a.
Proof.
  intros.
  destruct a.
  [true]: destruct b.
  [true.true]: reflexivity.
  [true.false]: reflexivity.
  [false]: reflexivity.
Qed.

Goal forall a b c : bool, a = a.
Proof.
  intros.
  destruct a.
  all: destruct b.
  all: destruct c.
  [true.true.true]: reflexivity.
  [true.true.false]: reflexivity.
  [true.false.true]: reflexivity.
  [true.false.false]: reflexivity.
  [false.true.true]: reflexivity.
  [false.true.false]: reflexivity.
  [false.false.true]: reflexivity.
  [false.false.false]: reflexivity.
Qed.
