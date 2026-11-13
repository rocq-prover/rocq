(* Two forms of the same primitive projection, one of them on an evar: when
   the projection has no canonical instance, their records are not unified
   before the other side is reduced. [X] below is [x], with [r + r] for the
   member, and not [half x] with [r]. *)
Set Primitive Projections.

Record total2 (A : Type) (P : A -> Type) := tpair { pr1 : A; pr2 : P pr1 }.
Arguments tpair {A P}.
Arguments pr1 {A P}.
Arguments pr2 {A P}.

Definition hProp := total2 Type (fun X => forall x y : X, x = y).
Definition hProptoType := @pr1 _ _ : hProp -> Type.
Coercion hProptoType : hProp >-> Sortclass.

Definition cuts := total2 (nat -> hProp) (fun _ => True).
Definition carrier (X : cuts) : nat -> hProp := pr1 X.
Coercion carrier : cuts >-> Funclass.

Definition half (x : cuts) : cuts := tpair (fun r => carrier x (r + r)) I.

Axiom cuts_bot : forall (X : cuts) (r : nat), pr1 X r -> forall q : nat, q <= r -> pr1 X q.
Axiom le_plus : forall r : nat, r <= r + r.

Goal forall (x : cuts) (r : nat), half x r -> x r.
Proof.
  intros x r Hr.
  apply cuts_bot with (1 := Hr).
  apply le_plus.
Qed.
