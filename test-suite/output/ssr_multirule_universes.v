(* The universes of the rules of a multirule that are not used by a
   rewrite step do not end up in the universe context of the proof *)

Require Import ssreflect.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Definition pid@{u} {A : Type@{u}} (x : A) : A := x.
Lemma pidE@{u} {A : Type@{u}} (x : A) : pid x = x.
Proof. reflexivity. Defined.
Axiom pax@{u} : forall {A : Type@{u}}, A -> A.
Axiom paxE@{u} : forall {A : Type@{u}} (x : A), pax x = x.
Definition pf@{u} {A : Type@{u}} (x y : A) : Prop := x = y.

Lemma multi@{i} (A : Type@{i}) (x : A) : pf (pid x) (pax x).
Proof.
rw (pidE, paxE).
(* Only the universe of the instance of [pidE] is added *)
Show Universes.
rw (pidE, paxE).
reflexivity.
Defined.
