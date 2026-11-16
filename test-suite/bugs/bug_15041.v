From Corelib Require Import ssrmatching ssreflect.

Goal true = true.
Proof.
apply: eq_trans.
set x := LHS.
Abort.

Goal true = true.
Proof.
apply: eq_trans.
ssrpattern LHS.
Abort.

Goal true = true.
Proof.
apply: eq_trans.
set x := (true as X in X = _).
Abort.

Goal true = true.
Proof.
apply: eq_trans.
set x := (true in X in X = _).
Abort.
