Require Import ssreflect.
Goal forall p : nat * nat , True.
Proof.
Fail case => x x.
Abort.
