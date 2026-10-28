(* The head of a pattern, here the left-hand side of a rewrite rule, is
   matched syntactically: its universe instance is equated with the one of
   the matched subterm, rather than related by weak constraints, here for
   the universe of a constructor of a cumulative inductive. The universe of
   the rule is hence substituted, and does not appear in the goal after the
   rewrite. *)

Require Import ssreflect.

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
Unset Universe Minimization ToSet.
Set Printing Universes.

Inductive tag@{u} : Set := Tag.

Definition tag_id@{u} (t : tag@{u}) : tag@{u} := t.

Lemma tagE@{u} : Tag@{u} = tag_id@{u} Tag@{u}.
Proof. reflexivity. Defined.

Lemma rw_irrelevant@{i} : @eq tag@{i} Tag@{i} Tag@{i}.
Proof. rw {1}tagE. Show. reflexivity. Defined.

(** As the head is matched syntactically, a rule instance naming another
    universe than the goal requires these universes to be already equal if rigid, 
    even when they are irrelevant (here for [Tag]) or when the head constant could be
    unfolded (here [pid]). *)

Lemma rw_ind_rigid@{i j|} : @eq tag@{i} Tag@{i} Tag@{i}.
Proof. Fail rw {1}tagE@{j}. rw {1}tagE. reflexivity. Defined.

Definition pid@{u} {A : Type@{u}} (x : A) : A := x.

Lemma pidE@{u} {A : Type@{u}} (x : A) : pid@{u} x = x.
Proof. reflexivity. Defined.

Lemma rw_const_rigid@{i j|} : pid@{i} 0 = 0.
Proof. Fail rw pidE@{j}. now rw pidE. Defined.

