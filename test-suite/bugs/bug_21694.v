Set Universe Polymorphism.

Section S.
  Sort s.

  Inductive foo@{s1 s2;u} (A:Type@{s2;u}) : Type@{s1;u} := X (_:A).

  Inductive bar (A:Type@{s;Set}) : Prop := Y (_:A).
End S.

Fail Definition bla (A:Type) (x:foo@{SProp Prop Type;_} A) : A := match x with X _ v => v end.

(* From Stdlib Require Import Hurkens. *)

(* Lemma bad : False. *)
(* Proof. *)
(*   unshelve eapply NoRetractFromSmallPropositionToProp.paradox. *)
(*   - exact (foo Prop). *)
(*   - apply X. *)
(*   - apply bla. *)
(*   - simpl. trivial. *)
(*   - simpl. trivial. *)
(* Qed. *)


Definition bla (A:Prop) (x:bar A) : A := match x with Y _ v => v end.
(* Anomaly "Quality γfoo.s undefined." *)
