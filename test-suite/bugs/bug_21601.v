Require Import TestSuite.jmeq.

(* in stdlib this is a consequence of axiom in Eqdep *)
Axiom JMeq_eq : forall (A:Type) (x y:A), JMeq x y -> x = y.

Abbreviation JMeq' := (fun A x => @JMeq A x A).

Polymorphic Lemma JMeq_ind_r@{s;+} : forall (A:Type) (x:A) (P:A -> Type@{s;_}),
   P x -> forall y, JMeq' A y x -> P y.
Proof.
intros A x P H y H'. destruct (JMeq_eq _ _ _ H'). assumption.
Qed.

Polymorphic Definition JMeq_leibniz_r@{s;u v w} : Has_Leibniz_r@{Type Prop s;u v w} JMeq' := JMeq_ind_r.

Hint Resolve JMeq_leibniz_r : rewrite_instances.

Goal forall A (x y : A), JMeq x y -> x = y.
intros A x y H.
rewrite H.
Abort.
