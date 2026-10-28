(* The head of a pattern, here the left-hand side of a rewrite rule, is
   matched syntactically: its universe instance is unified with the one of
   the matched subterm according to its variances, without weak
   constraints. An irrelevant universe, here the one of a constructor of a
   cumulative inductive, is unified when one of the two universes is
   flexible: the universe of the rule is hence substituted, and does not
   appear in the goal after the rewrite. *)

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

(** When both universes are rigid, an irrelevant universe is left
    unrelated: a rule naming another rigid universe than the goal still
    matches, without any constraint between them, both for [Tag] and for a
    constant whose universe only appears in its binders once applied (here
    [pid]). *)

Lemma rw_ind_rigid@{i j|} : @eq tag@{i} Tag@{i} Tag@{i}.
Proof. rw {1}tagE@{j}. rw {1}tagE. reflexivity. Defined.

Definition pid@{u} {A : Type@{u}} (x : A) : A := x.

Lemma pidE@{u} {A : Type@{u}} (x : A) : pid@{u} x = x.
Proof. reflexivity. Defined.

Lemma rw_const_rigid@{i j|} : pid@{i} 0 = 0.
Proof. rw pidE@{j}. reflexivity. Defined.

(** For an invariant universe, a flexible universe of the rule is also
    substituted, but two rigid universes must already be equal: a rule
    naming another rigid universe than the goal does not match. *)

Inductive itag@{=u} : Set := ITag.

Definition itag_id@{u} (t : itag@{u}) : itag@{u} := t.

Lemma itagE@{u} : ITag@{u} = itag_id@{u} ITag@{u}.
Proof. reflexivity. Defined.

Lemma rw_invariant@{i} : @eq itag@{i} ITag@{i} ITag@{i}.
Proof. rw {1}itagE. Show. reflexivity. Defined.

Lemma rw_inv_rigid_eq@{i} : @eq itag@{i} ITag@{i} ITag@{i}.
Proof. rw {1}itagE@{i}. Show. reflexivity. Defined.

Lemma rw_inv_rigid@{i j|} : @eq itag@{i} ITag@{i} ITag@{i}.
Proof. Fail rw {1}itagE@{j}. rw {1}itagE. reflexivity. Defined.
