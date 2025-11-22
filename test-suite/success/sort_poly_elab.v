Set Universe Polymorphism.

Inductive sum@{sl sr s;ul ur} (A : Type@{sl;ul}) (B : Type@{sr;ur}) : Type@{s;max(ul,ur)} :=
| inl : A -> sum A B
| inr : B -> sum A B.

Arguments inl {A B} _ , [A] B _.
Arguments inr {A B} _ , A [B] _.

(* Elimination constraint left explicitly empty. Definition fails because of missing constraint. *)
Fail Definition sum_elim@{sl sr s0 s0';ul ur v|}
  (A : Type@{sl;ul}) (B : Type@{sr;ur}) (P : sum@{sl sr s0;ul ur} A B -> Type@{s0';v})
  (fl : forall a, P (inl a)) (fr : forall b, P (inr b)) (x : sum@{sl sr s0;ul ur} A B) :=
    match x with
    | inl a => fl a
    | inr b => fr b
    end.
(* The command has indeed failed with message:
Elimination constraints are not implied by the ones declared: s0->s0' *)

(* Using + to elaborate missing constraints. Definition passes *)
Definition sum_elim@{sl sr s0 s0';ul ur v|+}
  (A : Type@{sl;ul}) (B : Type@{sr;ur}) (P : sum@{sl sr s0;ul ur} A B -> Type@{s0';v})
  (fl : forall a, P (inl a)) (fr : forall b, P (inr b)) (x : sum@{sl sr s0;ul ur} A B) :=
    match x with
    | inl a => fl a
    | inr b => fr b
    end.
(* sl sr s0 s0' ; ul ur v |= s0->s0' *)

Definition sum_sind := sum_elim@{Type Type Type SProp;_ _ _}.
Definition sum_rect := sum_elim@{Type Type Type Type;_ _ _}.
Definition sum_ind := sum_elim@{Type Type Type Prop;_ _ _}.

Definition or_ind := sum_elim@{Prop Prop Prop Prop;_ _ _}.
Definition or_sind := sum_elim@{Prop Prop Prop SProp;_ _ _}.
Fail Definition or_rect := sum_elim@{Prop Prop Prop Type;_ _ _}.
(* The command has indeed failed with message:
The quality constraints are inconsistent: cannot enforce Prop -> Type because it would identifyType and Prop which is inconsistent.
This is introduced by the constraints Type -> Prop *)

Definition sumor := sum@{Type Prop Type;_ _}.

Definition sumor_sind := sum_elim@{Type Prop Type SProp;_ _ _}.
Definition sumor_rect := sum_elim@{Type Prop Type Type;_ _ _}.
Definition sumor_ind := sum_elim@{Type Prop Type Prop;_ _ _}.

(* Implicit constraints are elaborated *)
Definition idT@{sl sr s;ul ur} (A : Type@{sl;ul}) (B : Type@{sr;ur}) (x : sum@{sl sr s;ul ur} A B)
  : sum@{sl sr Type;ul ur} A B :=
  match x return sum@{sl sr Type;ul ur} A B with
  | inl a => inl a
  | inr b => inr b
  end.
(* sl sr s ; ul ur |= s->Type *)

(* Implicit constraints are elaborated *)
Definition idP@{sl sr s;ul ur} (A : Type@{sl;ul}) (B : Type@{sr;ur}) (x : sum@{sl sr s;ul ur} A B)
  : sum@{sl sr Prop;ul ur} A B :=
  match x return sum@{sl sr Prop;ul ur} A B with
  | inl a => inl a
  | inr b => inr b
  end.
(* sl sr s ; ul ur |= s->Prop *)

(* Implicit constraints are elaborated *)
Definition idS@{sl sr s;ul ur} (A : Type@{sl;ul}) (B : Type@{sr;ur}) (x : sum@{sl sr s;ul ur} A B)
  : sum@{sl sr SProp;ul ur} A B :=
  match x return sum@{sl sr SProp;ul ur} A B with
  | inl a => inl a
  | inr b => inr b
  end.
(* sl sr s ; ul ur |= s->SProp *)

(* Implicit constraints are elaborated *)
Definition idV@{sl sr s s';ul ur} (A : Type@{sl;ul}) (B : Type@{sr;ur}) (x : sum@{sl sr s;ul ur} A B)
  : sum@{sl sr s';ul ur} A B :=
  match x return sum@{sl sr s';ul ur} A B with
  | inl a => inl a
  | inr b => inr b
  end.
(* sl sr s s' ; ul ur |= s->s' *)

Inductive List'@{s s';l} (A : Type@{s;l}) : Type@{s';l} :=
| nil' : List' A
| cons' : A -> List' A -> List' A.

Arguments nil' {A}.
Arguments cons' {A} _ _.

Definition list'_elim@{s s0 s';l l'}
  (A : Type@{s;l}) (P : List'@{s s0;l} A -> Type@{s';l'})
  (fn : P nil') (fc : forall (x : A) (l : List' A), P l -> P (cons' x l)) :=
  fix F (l : List'@{s s0;l} A) : P l :=
    match l with
    | nil' => fn
    | cons' x l => fc x l (F l)
    end.
(* s s0 s' ; l l' |= s0->s' *)

Fixpoint list'_idT@{s s';l} {A : Type@{s;l}} (l : List'@{s s';l} A) : List'@{s Type;l} A :=
  match l with
  | nil' => nil'
  | cons' x l => cons' x (list'_idT l)
  end.
(* s s' ; l |= s'->Type *)

Fixpoint list'_idP@{s s';l} {A : Type@{s;l}} (l : List'@{s s';l} A) : List'@{s Prop;l} A :=
  match l with
  | nil' => nil'
  | cons' x l => cons' x (list'_idP l)
  end.
(* s s' ; l |= s'->Prop *)

Fixpoint list'_idS@{s s';l} {A : Type@{s;l}} (l : List'@{s s';l} A) : List'@{s SProp;l} A :=
  match l with
  | nil' => nil'
  | cons' x l => cons' x (list'_idS l)
  end.
(* s s' ; l |= s'->SProp *)

(* Elimination constraint left explicitly empty. Definition fails because of missing constraint. *)
Fail Fixpoint list'_idV@{s s0 s';l l'|l <= l'} {A : Type@{s;l}} (l : List'@{s s0;l} A) : List'@{s s';l'} A :=
  match l with
  | nil' => nil'
  | cons' x l => cons' x (list'_idV l)
  end.
(* The command has indeed failed with message:
Elimination constraints are not implied by the ones declared: s0->s' *)

(* Using + to elaborate missing constraints. Definition passes *)
Fixpoint list'_idV@{s s0 s';l l'|l <= l' + } {A : Type@{s;l}} (l : List'@{s s0;l} A) : List'@{s s';l'} A :=
  match l with
  | nil' => nil'
  | cons' x l => cons' x (list'_idV l)
  end.
(* s s0 s' ; l l' |= s0->s', l <= l' *)


Inductive False'@{s;u} : Type@{s;u} :=.

Definition False'_False@{s; +|+} (x : False'@{s;_}) : False := match x return False with end.
(* s ; u |= s->Prop *)

Inductive bool@{s;u} : Type@{s;u} := true | false.

Definition bool_to_Prop@{s;u} (b : bool@{s;u}) : Prop.
Proof.
  destruct b.
  - exact True.
  - exact False.
Defined.
(* s ; u |= s->Type *)

Definition bool_to_True_conj@{s;u} (b : bool@{s;u}) : True \/ True.
Proof.
  destruct b.
  - exact (or_introl I).
  - exact (or_intror I).
Defined.
(* s ; u |= s->Prop *)

Program Definition bool_to_Prop'@{s;u} (b : bool@{s;u}) : Prop := _.
Next Obligation.
  intro b; destruct b.
  - exact True.
  - exact False.
Defined.
(* s ; u |= s->Type *)

Inductive unit@{s;u} : Type@{s;u} := tt.

#[universes(polymorphic=no)]
Sort Test.
Check (match true@{Test;Set} return ?[P] with true => tt | false => tt end).
