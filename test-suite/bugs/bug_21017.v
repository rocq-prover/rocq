Require Import ssreflect.

Lemma test T (a b c d : T) :
  (a, b) = (c, d) -> False.
Proof.
Fail move=> [^r].
Abort.
