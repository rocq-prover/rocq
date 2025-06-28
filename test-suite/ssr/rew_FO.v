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

Record foo := F { f : nat }.

Definition c := F (1 + 2).

Goal (forall x, 1 + (1 + x) = 5) -> 1 + f c = 1 + (1 + 7) .
Show.
move->.
Show.
match goal with |- 5 = 1 + (1 + 7) => idtac "ok" end.
Abort.

Goal (forall x, 1 + (1 + x) = 5) -> 1 + f c = 1 + (1 + 7) .
Show.
Set SsrMatching LegacyFoUnif.
move->.
Unset SsrMatching LegacyFoUnif.
Show.
match goal with |- 1 + f c = 5 => idtac "ok" end.
Abort.

Goal (forall x, 1 + (S x) = 5) -> 1 + f c = 1 + (1 + 7) .
Show.
move->.
Show.
match goal with |- 1 + f c = 1 + 5 => idtac "ok" end.
Abort.
