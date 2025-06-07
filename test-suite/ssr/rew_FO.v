From Corelib Require Import ssreflect.

Axiom R : Type.
Axiom op : nat -> R -> R -> R.

Axiom lemma : forall n x y z, op n (op n x y) z = z.

Arguments op {_} _ _.

Goal forall a b c : R, @op (0+1) (@op 1 a b) c =
                       @op 2 (@op 2 a b) c.
intros a b c.
Show.
rewrite lemma.
Show.
match goal with
| |- c = _ => idtac "ok"
end.
Abort.
