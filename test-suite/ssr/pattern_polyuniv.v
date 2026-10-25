(* Universe polymorphism and ssreflect patterns: the universe constraints
   obtained by matching patterns and rewrite rules must be recorded in the
   goal, and no universe should escape the scope of the proof. Lemmas are
   declared with non-extensible universe binders, so that any universe
   leaking from the matching machinery is reported as an error. *)

Require Import ssrmatching ssreflect.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Definition pid@{u} {A : Type@{u}} (x : A) : A := x.

Lemma pidE@{u} {A : Type@{u}} (x : A) : pid x = x.
Proof. reflexivity. Defined.

Definition pf@{u} {A : Type@{u}} (x y : A) : Prop := x = y.

(** Plain rewriting, with occurrences, repetition and patterns *)

Lemma rw_plain@{i} (A : Type@{i}) (x : A) : pf (pid x) x.
Proof. rw pidE. reflexivity. Defined.

Lemma rw_nested@{i} (A : Type@{i}) (x : A) : pf (pid (pid x)) x.
Proof. rw !pidE. reflexivity. Defined.

Lemma rw_occ@{i} (A : Type@{i}) (x : A) : pf (pid x) (pid x).
Proof. rw {2}pidE. rw {1}pidE. reflexivity. Defined.

Lemma rw_T@{i} (A : Type@{i}) (x : A) : pf (pid (pid x)) x.
Proof. rw [pid (pid _)]pidE. rw [pid _]pidE. reflexivity. Defined.

Lemma rw_in_T@{i} (A : Type@{i}) (x : A) : pf (pid x) (pid x).
Proof. rw [in pf _ _]pidE. reflexivity. Defined.

Lemma rw_X_in_T@{i} (A : Type@{i}) (x : A) : pf (pid (pid x)) (pid x).
Proof.
rw [X in pf X _]pidE. rw [X in pf _ X]pidE.
rw [X in pf X _]pidE. reflexivity.
Defined.

Lemma rw_in_X_in_T@{i} (A : Type@{i}) (x : A) : pf (pid (pid x)) (pid x).
Proof. rw [in X in pf X _]pidE. rw [in X in pf _ X]pidE. reflexivity. Defined.

Lemma rw_E_in_X_in_T@{i} (A : Type@{i}) (x : A) : pf (pid (pid x)) (pid x).
Proof.
rw [pid _ in X in pf X _]pidE. rw [pid x in X in pf _ X]pidE.
rw [pid _ in X in pf X _]pidE. reflexivity.
Defined.

Lemma rw_E_as_X_in_T@{i} (A : Type@{i}) (x : A) : pf (pid (pid x)) (pid x).
Proof.
rw [pid _ as X in pf X _]pidE. rw [pid _ as X in pf _ X]pidE.
rw [pid _ as X in pf X _]pidE. reflexivity.
Defined.

(** Several instances of the same polymorphic constant at different
    universe levels: the universe state must be threaded through all
    the occurrences *)

Lemma rw_levels@{i j | i < j +} (A : Type@{i}) (x : A) :
  pf@{j} (pid@{j} A) (pid@{j} (pid@{j} A)).
Proof.
rw [X in pf _ X]pidE. rw {1}pidE. rw pidE. reflexivity.
Defined.

Lemma rw_levels_occ@{i j | i < j +} (A : Type@{i}) (x : A) :
  pf@{j} (pid@{j} (pid@{j} A)) (pid@{j} (pid@{j} A)).
Proof. rw {1 2}pidE. rw !pidE. reflexivity. Defined.

(** Rules from a pair of equations, matched against the same pattern *)

Lemma pidE2@{u} {A : Type@{u}} (x y : A) :
  ((pid x = x) * (pid (pid y) = y))%type.
Proof. split; reflexivity. Defined.

Lemma rw_multi@{i} (A : Type@{i}) (x : A) : pf (pid (pid x)) (pid x).
Proof. rw [X in pf X _](pidE2 x x). rw (pidE2 x x). reflexivity. Defined.

(** Unfolding and folding, with and without patterns *)

Lemma unfold_fold@{i} (A : Type@{i}) (x : A) : pf (pid x) (pid x).
Proof.
rw /pid. rw -[x in X in pf X _]/(pid x).
rw [in X in pf X _]/pid. rw -[in X in pf _ X]/(pid x).
rw [X in pf _ X]/pid. reflexivity.
Defined.

Lemma unfold_E_as@{i} (A : Type@{i}) (x : A) : pf (pid (pid x)) x.
Proof. rw [pid _ as X in pf X _]/pid. reflexivity. Defined.

(** Pattern selection outside of rewriting *)

Lemma set_pat@{i} (A : Type@{i}) (x : A) : pf (pid (pid x)) (pid x).
Proof.
set w := {2}(pid x). set y := (pid _ in X in pf X _). set z := (X in pf X _).
rw /z /y /w !pidE. reflexivity.
Defined.

Lemma gen_pat@{i} (A : Type@{i}) (x : A) (P : A -> Prop) (P2 : A -> A -> Prop)
  (H : forall y, P y) (H2 : forall y, P2 y y) :
  P (pid (pid x)) /\ P2 (pid x) (pid x) /\ P (pid (pid x)).
Proof.
split; [|split].
- move: (X in P X). exact: H.
- move: {1 2}(pid _). exact: H2.
- move: (pid _ in X in P X). exact: H.
Defined.

Lemma ssrpattern_test@{i} (A : Type@{i}) (x : A) : pf (pid (pid x)) x.
Proof.
ssrpattern (pid (pid _)) => z.
rw /z !pidE. reflexivity.
Defined.

(** The resulting lemmas are usable at any level *)
Check rw_levels@{Set Type}.
Check rw_E_as_X_in_T@{Set}.
Check unfold_fold@{Set}.

(** Opaque constants: the instances of [pax] below are fresh flexible
    universes, they can only be rewritten together if the universe
    constraints obtained when matching each occurrence are recorded, and
    these universes must not escape the proof. *)

Axiom pax@{u} : forall {A : Type@{u}}, A -> A.
Axiom paxE@{u} : forall {A : Type@{u}} (x : A), pax x = x.

Lemma rw_occ_opaque@{i} (A : Type@{i}) (x : A) : True.
Proof.
have : pf (pax x) (pax x) /\ pf (pax (pax x)) (pax x).
  rw {1 2 4}paxE. rw !paxE. split; reflexivity.
by [].
Defined.

Lemma rw_X_in_T_opaque@{i} (A : Type@{i}) (x : A) : True.
Proof.
have : pf (pax (pax x)) (pax x).
  rw [X in pf X _]paxE. rw [X in pf _ X]paxE. rw [in X in pf X _]paxE.
  reflexivity.
by [].
Defined.

Lemma rw_E_in_X_in_T_opaque@{i} (A : Type@{i}) (x : A) : True.
Proof.
have : pf (pax (pax x)) (pax x) /\ pf (pax x) (pax x).
  rw [pax (pax x) as X in pf X _]paxE. rw [pax _ in X in pf X _]paxE.
  rw !paxE. split; reflexivity.
by [].
Defined.

Lemma set_gen_opaque@{i} (A : Type@{i}) (x : A) (P : A -> A -> Prop)
  (H : forall y, P y y) : True.
Proof.
have : P (pax x) (pax x) /\ P (pax (pax x)) (pax (pax x)).
  by split; [set y := pax _ | move: (pax _ in X in P X X)]; exact: H.
by [].
Defined.

(** [e as X in T] patterns where [e] has holes: building [T{X := e}] used to
    unify the type of [X] with the one of [e], creating a type evar whose
    sort is never bounded from below and prevented minimizing the universes
    of the goal, which then escaped the proof. *)

Lemma rw_E_as_holes_opaque@{i} (A : Type@{i}) (x : A) : True.
Proof.
have : pf (pax (pax x)) (pax x).
  rw [pax _ as X in pf X _]paxE. rw !paxE. reflexivity.
have : pf (pax (pax x)) (pax x).
  rw [_ as X in pf X _]paxE. rw !paxE. reflexivity.
by [].
Defined.

Lemma set_gen_E_as_holes_opaque@{i} (A : Type@{i}) (x : A) (P : A -> A -> Prop)
  (H : forall y, P y y) : True.
Proof.
have : P (pax (pax x)) (pax (pax x)).
  set y := (pax _ as X in P X _). exact: H.
have : P (pax (pax x)) (pax (pax x)).
  move: (pax _ as X in P X X). exact: H.
by [].
Defined.
