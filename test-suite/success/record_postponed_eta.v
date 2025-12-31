
Set Primitive Projections.

Fail #[warnings="+non-primitive-record"]
Record RTypeToSProp (A : SProp) : Type := {
  f1 : A
}.
(* The record RTypeToSProp could not be defined as a primitive record because it is not in SProp but all projections may be irrelevant. *)

Fail #[warnings="+non-primitive-record"]
Record RPropToSProp (A : SProp) : Prop := {
  f2 : A
}.
(* The record RTypeToProp could not be defined as a primitive record because it is not in SProp but all projections may be irrelevant. *)

Set Universe Polymorphism.

Record RSToSProp@{s;u|s -> SProp} (A : SProp) : Type@{s;u} := {
  f3 : A
}.

Inductive eq@{s s'; u} (A : Type@{s;u}) (a : A) : A -> Prop :=
  eq_refl : eq A a a.

Arguments eq {_}.
Arguments eq_refl {_ _}.

(* Conversion when record is in Type and field in SProp fails correctly *)
Goal forall (A:SProp) (r2 : RSToSProp@{Type;0} A), eq r2 {| f3 := r2.(f3 A) |}.
Proof. intros A r2. Fail reflexivity. Abort.
(* The command has indeed failed with message:
    In environment
    A : SProp
    r2 : RSToProp A
    Unable to unify "{| f3 := f3 _ r2 |}" with "r2". *)

(* Conversion when record and field are instantiated to SProp checks correctly *)
Goal forall (A:SProp) (r2 : RSToSProp@{SProp;0} A), eq r2 {| f3 := r2.(f3 A) |}.
Proof. intros A r2. reflexivity. Qed.

Record RSToS'@{s1 s2;u1 u2| s2 -> s1 +} (A : Type@{s1;u1}): Type@{s2;u2} := {
  f4 : A
}.

(* Conversion when record is in Type and field in SProp fails correctly *)
Goal forall (A:SProp) (r2 : RSToS'@{SProp Type;0 0} A), eq r2 {| f4 := r2.(f4 A) |}.
Proof. intros A r2. Fail reflexivity. Abort.
(* The command has indeed failed with message:
  In environment
  A : SProp
  r2 : RSToS' A
  Unable to unify "{| f4 := f4 _ r2 |}" with "r2". *)

(* Conversion when record is in Prop and field in SProp fails correctly *)
Goal forall (A:SProp) (r2 : RSToS'@{SProp Prop;0 0} A), eq r2 {| f4 := r2.(f4 A) |}.
Proof. intros A r2. Fail reflexivity. Abort.
(* The command has indeed failed with message:
  In environment
  A : SProp
  r2 : RSToS' A
  Unable to unify "{| f4 := f4 _ r2 |}" with "r2". *)

(* Conversion when record and field are instantiated to SProp checks correctly *)
Goal forall (A:SProp) (r2 : RSToS'@{SProp SProp;0 0} A), eq r2 {| f4 := r2.(f4 A) |}.
Proof. intros A r2. reflexivity. Qed.

(* Conversion when record and field are instantiated to the same sort (Type) checks correctly *)
Goal forall (A:Set) (r2 : RSToS'@{Type Type;0 0} A), eq r2 {| f4 := r2.(f4 A) |}.
Proof. intros A r2. reflexivity. Qed.

(* Conversion when record and field are instantiated to the same sort (Prop) checks correctly *)
Goal forall (A:Prop) (r2 : RSToS'@{Prop Prop;0 0} A), eq r2 {| f4 := r2.(f4 A) |}.
Proof. intros A r2. reflexivity. Qed.

(* Conversion when record is in Type and field is in Prop checks correctly *)
Goal forall (A:Prop) (r2 : RSToS'@{Prop Type;0 0} A), eq r2 {| f4 := r2.(f4 A) |}.
Proof. intros A r2. reflexivity. Qed.

Section Sorts.
  Sort s s'.

  Constraint s -> SProp.

  (* Conversion when record is in Type and field in SProp fails correctly *)
  Goal forall (A:SProp) (r2 : RSToSProp@{s;0} A), eq r2 {| f3 := r2.(f3 A) |}.
  Proof. intros A r2. Fail reflexivity. Abort.
  (* The command has indeed failed with message:
    In environment
    A : SProp
    r2 : RSToProp A
    Unable to unify "{| f3 := f3 _ r2 |}" with "r2". *)

  Constraint s' -> s.

  (* Conversion when record and field are instantiated to the different sorts fails correctly *)
  Goal forall (A:Type@{s;0}) (r2 : RSToS'@{s s';0 0} A), eq r2 {| f4 := r2.(f4 A) |}.
  Proof. intros A r2. Fail reflexivity. Abort.
  (* The command has indeed failed with message:
    In environment
    A : Type@{s ; _}
    r2 : RSToS' A
    Unable to unify "{| f4 := f4 _ r2 |}" with "r2". *)

  (* Conversion when record and field are instantiated to the same sort (Type) checks correctly *)
  Goal forall (A:Type@{s;0}) (r2 : RSToS'@{s s;0 0} A), eq r2 {| f4 := r2.(f4 A) |}.
  Proof. intros A r2. reflexivity. Qed.
End Sorts.
