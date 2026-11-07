(* Universe polymorphism and the patterns of case/elim: each pattern is
   added to the evar map of the elimination as an extension, and no
   universe should escape the scope of the proof. Lemmas are declared with
   non-extensible universe binders, so that any universe leaking from the
   matching machinery is reported as an error. *)

Require Import ssreflect.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Definition pid@{u} {A : Type@{u}} (x : A) : A := x.

Definition pf@{u} {A : Type@{u}} (x y : A) : Prop := x = y.

Inductive spec@{u} {A : Type@{u}} (x : A) : A -> Prop := Spec : spec x x.

Lemma pidP@{u} {A : Type@{u}} (x : A) : spec x (pid x).
Proof. exact: Spec. Defined.

Inductive spec2@{u} {A : Type@{u}} (x : A) : A -> A -> Prop :=
  Spec2 : spec2 x x x.

Lemma pid2P@{u} {A : Type@{u}} (x : A) : spec2 x (pid x) (pid (pid x)).
Proof. exact: Spec2. Defined.

(** Inferred patterns only *)

Lemma case_inferred@{i} (A : Type@{i}) (x : A) : pf (pid x) x.
Proof. case: (pidP x). reflexivity. Defined.

(** A user pattern, matched in the goal *)

Lemma case_T@{i} (A : Type@{i}) (x : A) : pf (pid x) x.
Proof. case: (pid x) / (pidP x). reflexivity. Defined.

Lemma case_T_wild@{i} (A : Type@{i}) (x : A) : pf (pid x) x.
Proof. case: (pid _) / (pidP x). reflexivity. Defined.

Lemma case_occ@{i} (A : Type@{i}) (x : A) : pf (pid x) (pid x).
Proof. case: {2}(pid x) / (pidP x). reflexivity. Defined.

Lemma case_X_in_T@{i} (A : Type@{i}) (x : A) : pf (pid x) (pid x).
Proof. case: (X in pf _ X) / (pidP x). reflexivity. Defined.

(** A user pattern which does not occur in the goal *)

Lemma case_nomatch@{i} (A : Type@{i}) (x : A) : pf x x.
Proof. case: (pid x) / (pidP x). reflexivity. Defined.

(** A wildcard pattern, postponed until the other one is matched *)

Lemma case_postponed@{i} (A : Type@{i}) (x : A) : pf (pid x) (pid (pid x)).
Proof. case: _ (pid (pid x)) / (pid2P x). reflexivity. Defined.

(** Several patterns, with a pattern at another universe level *)

Lemma case_two_levels@{i j} (A : Type@{i}) (B : Type@{j}) (x : A) (y : B) :
  pf (pid x) x /\ pf (pid y) y.
Proof.
case: (pid x) / (pidP x). case: (pid y) / (pidP y).
split; reflexivity.
Defined.

(** An equation, generalized by a tactic running before the elimination *)

Lemma case_eq@{i} (A : Type@{i}) (x : A) : pf (pid x) x.
Proof. case E: (pid x) / (pidP x). reflexivity. Defined.

Lemma elim_eq@{i} (A : Type@{i}) (x : A) : pf (pid x) x.
Proof. elim E: (pid x) / (pidP x). reflexivity. Defined.
