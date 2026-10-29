(* Multirule rewrites without universe polymorphism *)

Require Import ssreflect ssrfun ssrbool.

Axiom f g : nat -> nat.
Axiom fE : forall n, f n = n.
Axiom gE : forall n, g n = n.

Definition idt {A : Type} (x : A) := x.
Lemma idtE {A : Type} (x : A) : idt x = x. Proof. by []. Qed.

(** Only the first match is rewritten by a step, [!] rewrites them all *)

Lemma rw_multi_once : f 0 = g 0.
Proof. rw (fE, gE). change (0 = g 0). rw (fE, gE). reflexivity. Qed.

Lemma rw_multi_bang : f (g 0) + idt (g (f 1)) = 0 + 1.
Proof. rw !(fE, gE, idtE). reflexivity. Qed.

Lemma rw_multi_pattern : f (g 0) = g (f 0).
Proof. rw [X in _ = X](gE, fE). change (f (g 0) = f 0). rw !(fE, gE). reflexivity. Qed.

(** A monomorphic constant used at a term level and at a type level within
    the same multirule *)

Lemma rw_multi_levels (b : idt bool) : idt (idt nat) = nat /\ idt b = b.
Proof. by rw !(idtE, fE). Qed.

(** Rules sharing an evar, from a lemma [forall x, A x * B x]; only the side
    condition of the rule which is used becomes a goal *)

Axiom fgE : forall n, (f n = n) * (g n = n).
Axiom P Q : nat -> Prop.
Axiom fgPQ : forall n, (P n -> f n = n) * (Q n -> g n = n).

Lemma rw_multi_shared : f 0 + g 1 + f 1 = 0 + 1 + 1.
Proof.
rw fgE. change (0 + g 1 + f 1 = 0 + 1 + 1).
rw !fgE. reflexivity.
Qed.

Lemma rw_multi_side_conditions (P0 : P 0) (Q1 : Q 1) : f 0 + g 1 = 0 + 1.
Proof.
(* Exactly one side condition each time *)
rw fgPQ; [ | ]; try exact P0.
rw fgPQ; [ | ]; try exact Q1.
reflexivity.
Qed.

(** A multirule whose rule has holes typed by universes defined during its
    interpretation (the shape of mathcomp's [size_pmap_sub]) *)

Fixpoint count {T : Type} (a : pred T) (s : list T) : nat :=
  match s with nil => 0 | cons x s' => (if a x then 1 else 0) + count a s' end.

Lemma eq_count {T : Type} {a1 a2 : pred T} : a1 =1 a2 -> count a1 =1 count a2.
Proof. by move=> E; elim=> //= x s ->; rw E. Qed.

Structure subType {T : Type} (P : pred T) :=
  SubType { sub_sort :> Type; insub : T -> option sub_sort;
            isSome_insub_ax : (fun x => isSome (insub x)) =1 P }.

Lemma isSome_insub {T : Type} {P : pred T} (sT : subType P) :
  (fun x => isSome (@insub T P sT x)) =1 P.
Proof. exact: isSome_insub_ax. Qed.

Section S.
Variables (T : Type) (p : pred T) (sT : subType p).

Lemma rw_multi_universe_subst s :
  count (fun x => isSome (@insub _ _ sT x)) s + f 0 = count p s + 0.
Proof. by rw !(eq_count (isSome_insub _), fE). Qed.
End S.

(** Template polymorphic types: the universes of [list] and [prod] *)

Lemma rw_multi_template (l : list (nat * bool)) :
  idt (cons (f 0, true) l) = cons (g 0, idt true) (idt l).
Proof. by rw !(fE, gE, idtE). Qed.
