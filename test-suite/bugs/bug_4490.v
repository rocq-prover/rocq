Require Import ListDef Morphisms.

Definition list_caset A (P : list A -> Type) (N : P nil) (C : forall x xs, P (x::xs))
             ls
  : P ls
    := match ls with
         | nil => N
         | x::xs => C x xs
       end.

Global Instance list_caset_Proper {A P}
: Proper (eq
            ==> pointwise_relation _ (pointwise_relation _ eq)
            ==> pointwise_relation _ eq)
         (@ list_caset A (fun _ => P)).
Proof.
  lazy.
  intros ??? ?? H [|? ?]; subst; eauto.
Qed.

Global Instance list_caset_Proper' {A P}
: Proper (eq
            ==> pointwise_relation _ (pointwise_relation _ eq)
            ==> eq
            ==> eq)
         (@ list_caset A (fun _ => P)).
Proof.
  lazy.
  intros ??? ?? H [|? ?] ??; subst; eauto.
Qed.

Goal True.
Proof.
  Succeed let P := nat in
  let A := nat in
  pose proof (_ : Proper (@ eq P ==> pointwise_relation A (pointwise_relation _ eq) ==> _ ==> _) (@ list_caset A (fun _ => P))).
  Succeed let P := nat in
  let A := nat in
  pose proof (_ : Proper (@ eq P ==> pointwise_relation A _ ==> _ ==> _) (@ list_caset A (fun _ => P))).
Abort.
