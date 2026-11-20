Require Import ssreflect.

Inductive vec : nat -> Type :=
| vnil : vec 0
| vcons n : nat -> vec n -> vec (S n).

Axiom P : forall n, vec n -> Prop.

Goal forall n (v : vec n), P n v.
Proof.
move=> n v.
Fail case: n.
Fail elim: n.
Fail case E: n.
Fail elim E: n.
case: n / v.
Abort.

Goal forall n (v : vec n), n = n -> P n v.
Proof.
move=> n v.
case: {2}n.
Abort.
