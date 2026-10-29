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

(** Multi-rule rewrites: only the rule that is used may contribute
    universes and constraints, the failed attempts at matching the other
    rules must not leave any constraint behind. *)

Lemma rw_multi_lemmas@{i} (A : Type@{i}) (x : A) : pf (pid x) (pax x).
Proof. rw (pidE, paxE). rw (pidE, paxE). reflexivity. Defined.

Lemma rw_multi_bang@{i} (A : Type@{i}) (x : A) : pf (pax (pid x)) (pid (pax x)).
Proof. rw !(pidE, paxE). reflexivity. Defined.

Lemma rw_multi_pattern@{i} (A : Type@{i}) (x : A) : pf (pax (pid x)) (pid (pax x)).
Proof.
rw [X in pf _ X](paxE, pidE). rw [pax _ in X in pf X _](pidE, paxE).
rw (pidE, paxE). reflexivity.
Defined.

(* The first rule cannot match without equating [i] with [Set] *)
Lemma rw_multi_fixed@{i} (A : Type@{i}) (x : A) : pf (pid x) x.
Proof. rw (pidE@{Set}, pidE). reflexivity. Defined.

(* The first rule cannot match without equating [i] and [j], which would
   contradict [i < j] *)
Lemma rw_multi_levels@{i j | i < j +} (A : Type@{i}) (x : A) :
  pf@{j} (pid@{j} A) A.
Proof. rw (@pidE@{i}, @pidE@{j}). reflexivity. Defined.

(* An opaque product of rules is used through projections *)
Lemma pidE2o@{u} {A : Type@{u}} (x y : A) :
  ((pid x = x) * (pid (pid y) = y))%type.
Proof. split; reflexivity. Qed.

Lemma rw_multi_opaque@{i} (A : Type@{i}) (x : A) : pf (pid x) (pax x).
Proof. rw (pidE2o x x, paxE). rw (pidE2o x x, paxE). reflexivity. Defined.

Lemma rw_multi_flex@{i} (A : Type@{i}) (x : A) : True.
Proof.
have : pf (pax (pid x)) (pid (pax x)) /\ pf (pid (pax x)) (pax (pid x)).
  rw !(pidE, paxE). split; reflexivity.
by [].
Defined.

(** Multirule rewrites on instances of a constant at incompatible universe
    levels: an instance of a rule matched at [u] cannot be used at [v] when
    [u < v], those occurrences are not rewritten (and no inconsistent
    constraint is added), but [!] rewrites them using a fresh instance of
    the rule. *)

Axiom foo@{i} : nat.
Axiom bar@{i} : nat.
Axiom fooE@{i} : foo@{i} = 0.
Axiom barE@{i} : bar@{i} = 0.

Lemma rw_incompatible@{u v | u < v} : foo@{u} = foo@{v}.
Proof.
rw (fooE, barE). change (0 = foo@{v}).
rw (fooE, barE). reflexivity.
Defined.

Lemma rw_incompatible_rev@{u v | u < v} : foo@{v} = foo@{u}.
Proof.
rw (fooE, barE). change (0 = foo@{u}).
rw (fooE, barE). reflexivity.
Defined.

Lemma rw_bang_incompatible@{u v | u < v} : foo@{u} + bar@{v} = foo@{v} + bar@{u}.
Proof. rw !(fooE, barE). reflexivity. Defined.

Lemma rw_bang_incompatible_interleaved@{u v | u < v} :
  foo@{u} + foo@{v} + foo@{u} = bar@{v} + foo@{v} + bar@{u}.
Proof. rw !(fooE, barE). reflexivity. Defined.

(** Multirules whose rules share evars, e.g. obtained from a lemma
    [forall x, A x * B x]: only the evars (side conditions) and universes of
    the rule which is used end up in the proof. *)

Axiom fs@{u} : forall {A : Type@{u}}, A -> A.
Axiom gs@{u} : forall {A : Type@{u}}, A -> A.
Axiom Ps@{u} : forall {A : Type@{u}}, A -> Prop.
Axiom Qs@{u} : forall {A : Type@{u}}, A -> Prop.

(* The two rules share the evar for [x] *)
Axiom fgsE : forall (A : Type) (x : A), (fs x = x) * (gs x = x).

Lemma rw_multi_shared_once@{i} (A : Type@{i}) (a : A) : fs@{i} a = gs@{i} a.
Proof.
rw fgsE. change (a = gs@{i} a).
rw fgsE. reflexivity.
Defined.

Lemma rw_multi_shared_bang@{i} (A : Type@{i}) (a : A) : fs@{i} (gs@{i} a) = gs@{i} (fs@{i} a).
Proof. rw !fgsE. reflexivity. Defined.

(* Rules with premises sharing the evar for [x]: only the premise of the
   rule which is used becomes a new goal *)
Axiom fgsPQ : forall (A : Type) (x : A), (Ps x -> fs x = x) * (Qs x -> gs x = x).

Lemma rw_multi_side_conditions (A : Type) (a : A) (Pa : Ps a) (Qa : Qs a) : fs a = gs a.
Proof.
(* Exactly one side condition each time *)
rw fgsPQ; [ | ]; try exact Pa.
rw fgsPQ; [ | ]; try exact Qa.
reflexivity.
Qed.

Lemma rw_multi_side_conditions_bang (A : Type) (a : A) (Pa : Ps a) (Qa : Qs a) : fs a = gs a.
Proof.
rw !fgsPQ; [ | | ]; try exact Pa; try exact Qa.
reflexivity.
Qed.

(** A multirule [forall x, A x * B x] with matches for both rules at
    incompatible instances of [x] in the same traversal: a rewrite step only
    uses the first match, for all its occurrences, the other rule being used
    with a fresh [x] by the following steps. *)

Axiom Ax Bx : nat -> nat.
Axiom ABxE : forall x : nat, (Ax x = x) * (Bx x = x).

Lemma rw_multi_shared_instances : Ax 0 + Bx 1 + Ax 0 + Ax 1 = 0 + 1 + 0 + 1.
Proof.
rw ABxE. change (0 + Bx 1 + 0 + Ax 1 = 0 + 1 + 0 + 1).
rw ABxE. change (0 + 1 + 0 + Ax 1 = 0 + 1 + 0 + 1).
rw ABxE. reflexivity.
Qed.

Lemma rw_multi_shared_instances_rev : Bx 1 + Ax 0 = 1 + 0.
Proof.
rw ABxE. change (1 + Ax 0 = 1 + 0).
rw ABxE. reflexivity.
Qed.

Lemma rw_multi_shared_instances_bang : Ax 0 + Bx 1 + Ax 1 + Bx 0 = 0 + 1 + 1 + 0.
Proof. rw !ABxE. reflexivity. Qed.
