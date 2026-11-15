Require Import ssreflect.

Axiom x : nat.

Goal Nat.eqb (x + x + x) (3 * x) = true.
Proof.
Fail set f := (fun x => X in X = true).
Fail set f := (x + x as x + x).
set f := (X in X = true).
Abort.
