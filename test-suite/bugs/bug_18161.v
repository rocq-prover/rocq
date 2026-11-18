Require Import ssreflect.

Axiom foo : {i : nat | i = 0}.

Lemma bar : (let (x, _) := foo in x) = 0.
Proof.
Fail unlock foo.
Abort.
