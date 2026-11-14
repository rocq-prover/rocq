From Corelib Require Import ssreflect.

Definition b2n (b : bool) := if b then 1 else 0.
Definition leq m n := Nat.eqb (m - n) 0.
Definition addn := Nat.add.
Axiom F : (nat -> nat) -> Prop.

Goal F (fun i => addn (b2n (leq 0 i)) i).
Proof.
rewrite /(addn 1).
match goal with |- F (fun i => 1 + i) => idtac end.
Abort.

Axiom f : nat -> nat.
Axiom L : f 0 = 1.

Goal (fun n : nat => f (fst (0, n))) = (fun _ => 1).
Proof.
Fail rewrite L.
Abort.
