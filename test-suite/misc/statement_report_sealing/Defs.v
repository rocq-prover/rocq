(* Objects for misc/statement_report_sealing.sh, compiled with -noinit. For
   each row, a model [m_*], a trusted constant [t_<row>] and a module type
   [S_<row>] whose field [f] has the trusted constant's type and universes. *)

Inductive unit : Set := tt.

Universe a b c d e.
Constraint e < d.
Sort q.
Universe qa qb qc qd.
Constraint qd < qc.
Universe ma mb.
Constraint ma < mb.

Definition m_same : forall _ : Type@{a}, Type@{a} := fun A => A.
Definition m_set : Set := unit.
Definition m_prop : Prop := forall P : Prop, P.
Parameter m_indep : Type@{b}.
Parameter m_incons : Type@{d}.
Parameter m_qsort : Univ@{q;qa}.
Parameter m_qsort_lt : Univ@{q;qc}.
Parameter m_alg : forall _ : Type@{max(a,b)}, Set.
Polymorphic Definition m_poly@{u} : forall _ : Type@{u}, Type@{u} := fun A => A.
Polymorphic Definition m_poly_lt@{u v | u < v} : forall _ : Type@{u}, Type@{v} := fun A => A.
Polymorphic Definition m_poly_le@{u v | u <= v} : forall _ : Type@{u}, Type@{v} := fun A => A.
Polymorphic Definition m_two@{u v | u <= v} (A : Type@{u}) (B : Type@{v}) : Set := unit.
Polymorphic Parameter m_poly_univ@{u v|} : Type@{u}.
Polymorphic Definition m_poly_sort@{s;u|} (A : Univ@{s;u}) (x : A) : A := x.
Definition m_fun : forall _ : Set, Set := fun A => A.
Monomorphic Definition m_implicit {A : Set} (x : A) : A := x.
Definition m_binder : forall _ : unit, Set := fun _ => unit.

(* The same type. *)
Parameter t_same : forall _ : Type@{a}, Type@{a}.
Module Type S_same. Parameter f : forall _ : Type@{a}, Type@{a}. End S_same.

(* [Set] is below every [Type]. *)
Parameter t_set_type : Type@{a}.
Module Type S_set_type. Parameter f : Type@{a}. End S_set_type.

(* [Prop] is below every [Type]. *)
Parameter t_prop_type : Type@{a}.
Module Type S_prop_type. Parameter f : Type@{a}. End S_prop_type.

(* Unrelated universes: sealing adds [b <= c]. *)
Parameter t_indep : Type@{c}.
Module Type S_indep. Parameter f : Type@{c}. End S_indep.

(* [d <= e] contradicts [e < d]. *)
Parameter t_incons : Type@{e}.
Module Type S_incons. Parameter f : Type@{e}. End S_incons.

(* One global sort quality, unrelated universes: sealing adds [qa <= qb]. *)
Parameter t_qsort : Univ@{q;qb}.
Module Type S_qsort. Parameter f : Univ@{q;qb}. End S_qsort.

(* [qc <= qd] contradicts [qd < qc]. *)
Parameter t_qsort_lt : Univ@{q;qd}.
Module Type S_qsort_lt. Parameter f : Univ@{q;qd}. End S_qsort_lt.

(* Product domains are compared for equality, and an algebraic universe
   cannot be made equal to a level. *)
Parameter t_alg : forall _ : Type@{c}, Set.
Module Type S_alg. Parameter f : forall _ : Type@{c}, Set. End S_alg.

(* A polymorphic model at a monomorphic statement: one instance of it. *)
Parameter t_poly_mono : forall _ : Type@{a}, Type@{a}.
Module Type S_poly_mono. Parameter f : forall _ : Type@{a}, Type@{a}. End S_poly_mono.

(* The definition declares the model's fresh universe as a global one, which is
   strictly above Set, so it cannot be taken as Set. *)
Parameter t_poly_set : forall _ : Set, Set.
Module Type S_poly_set. Parameter f : forall _ : Set, Set. End S_poly_set.

(* The kernel accepts the model as the field, but the reference does not
   elaborate: its maximal implicit argument stays unresolved. *)
Polymorphic Parameter t_implicit : forall (A : Set) (_ : A), A.
Module Type S_implicit. Polymorphic Parameter f : forall (A : Set) (_ : A), A. End S_implicit.

(* The model's [u < v] contradicts the instance [u = v = a]. *)
Parameter t_poly_mono_lt : forall _ : Type@{a}, Type@{a}.
Module Type S_poly_mono_lt. Parameter f : forall _ : Type@{a}, Type@{a}. End S_poly_mono_lt.

(* The instance [u = ma], [v = mb] satisfies the model's [u <= v], but
   elaborating the alias can minimize [v] to [u], which [ma < mb] refuses. *)
Parameter t_poly_mono_le : forall (A : Type@{ma}) (B : Type@{mb}), Set.
Module Type S_poly_mono_le. Parameter f : forall (A : Type@{ma}) (B : Type@{mb}), Set. End S_poly_mono_le.

(* Polymorphic on both sides. *)
Polymorphic Parameter t_poly_poly@{u} : forall _ : Type@{u}, Type@{u}.
Module Type S_poly_poly. Polymorphic Parameter f@{u} : forall _ : Type@{u}, Type@{u}. End S_poly_poly.

(* The model needs [u < v]; the statement does not give it. *)
Polymorphic Parameter t_poly_lt@{u v} : forall _ : Type@{u}, Type@{v}.
Module Type S_poly_lt. Polymorphic Parameter f@{u v} : forall _ : Type@{u}, Type@{v}. End S_poly_lt.

(* The statement's [u < v] implies the model's [u <= v]. *)
Polymorphic Parameter t_poly_strong@{u v | u < v} : forall _ : Type@{u}, Type@{v}.
Module Type S_poly_strong.
  Polymorphic Parameter f@{u v | u < v} : forall _ : Type@{u}, Type@{v}.
End S_poly_strong.

(* The same context on both sides; elaborating the alias can minimize [v] to [u]. *)
Polymorphic Parameter t_poly_le_le@{u v | u <= v} : forall _ : Type@{u}, Type@{v}.
Module Type S_poly_le_le.
  Polymorphic Parameter f@{u v | u <= v} : forall _ : Type@{u}, Type@{v}.
End S_poly_le_le.

(* Contexts agree, but the types need [u <= v], which the statement does not give. *)
Polymorphic Parameter t_poly_univ@{u v|} : Type@{v}.
Module Type S_poly_univ. Polymorphic Parameter f@{u v|} : Type@{v}. End S_poly_univ.

(* Sort-polymorphic on both sides; elaborating the alias can collapse the
   model's quality binder. *)
Polymorphic Parameter t_poly_sort@{s;u|} : forall (A : Univ@{s;u}) (_ : A), A.
Module Type S_poly_sort.
  Polymorphic Parameter f@{s;u|} : forall (A : Univ@{s;u}) (_ : A), A.
End S_poly_sort.

(* A monomorphic model at a polymorphic statement without universes. *)
Polymorphic Parameter t_mono_poly : Set.
Module Type S_mono_poly. Polymorphic Parameter f : Set. End S_mono_poly.

(* Another statement. *)
Parameter t_different : forall _ : unit, Set.
Module Type S_different. Parameter f : forall _ : unit, Set. End S_different.

(* One binder fewer. *)
Parameter t_binder : Set.
Module Type S_binder. Parameter f : Set. End S_binder.
