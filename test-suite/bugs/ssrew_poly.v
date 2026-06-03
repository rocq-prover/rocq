From Corelib Require Import ssreflect.

Axiom foo@{i} : unit.
Set Printing Universes.
About foo.

Axiom lemma@{i} : foo@{i} = tt.

Lemma test : foo@{0} = foo@{1}.
Proof.
  rw !lemma. reflexivity.
Qed.
