
Require Import Ltac2.Ltac2.

Axiom plus: nat -> nat -> nat.

Declare Custom Entry foo.

Definition enter{T: Type}: T -> T := @id T.

Notation "a +++ b" := (plus a b) (in custom foo at level 5, a custom foo, b custom foo).
Notation "x" := x (in custom foo at level 0, x ident).
Notation "{{ x }}" := (enter x) (x custom foo at level 5).

Ltac2 Notation "go" "(" a(constr(custom(foo))) ")" := pose $a as x.

Goal forall (p q: nat), False.
Proof.
  intros.
  go (p +++ q).
Abort.
