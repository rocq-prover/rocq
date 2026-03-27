
(* variances other than Invariant are forbidden for non-cumul inductives *)
Fail Inductive foo@{+u} : Prop := .
Fail Polymorphic Inductive foo@{*u} : Prop := .
Inductive foo@{=u} : Prop := .

(* Cumulative attr forbidden without univ poly on *)
Fail Cumulative Inductive bar@{u} : Prop := .

(* option allowed but does nothing until univ poly is on *)
Set Polymorphic Inductive Cumulativity.

Fail Inductive bar@{*u} : Prop := .
Succeed Polymorphic  Inductive bar@{*u} : Prop := .

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

Inductive force_invariant@{=u} : Prop := .
Fail Definition lift@{u v | u < v} (x:force_invariant@{u}) : force_invariant@{v} := x.

Inductive force_covariant@{+u} : Prop := .
Fail Definition lift@{u v | v < u} (x:force_covariant@{u}) : force_covariant@{v} := x.
Definition lift@{u v | u < v} (x:force_covariant@{u}) : force_covariant@{v} := x.

Fail Inductive not_irrelevant@{*u} : Prop := nirr (_ : Type@{u}).
Inductive check_covariant@{+u} : Prop := cov (_ : Type@{u}).

Fail Inductive not_covariant@{+u} : Prop := ncov (_ : Type@{u} -> nat).

Inductive must_unfold@{+u *v} : Prop := cmust (_ : @id Type@{v} Type@{u}).

Inductive actually_default_unfold@{u v} : Prop := cnodef (_ : @id Type@{v} Type@{u}).
Inductive actually_default_unfold_check@{+u *v} : Prop
  := cnodef_check (_ : actually_default_unfold@{u v}).


Inductive irrelevant@{*u} : Prop := .

(* weak constraints help minimization *)
Definition irrelevant_with_weak@{u} : irrelevant@{u} -> irrelevant := fun x => x.

Unset Cumulativity Weak Constraints.
Fail Definition irrelevant_without_weak@{u} : irrelevant@{u} -> irrelevant := fun x => x.
Definition irrelevant_without_weak@{u+} : irrelevant@{u} -> irrelevant := fun x => x.
Check irrelevant_without_weak@{_ _}.

(* sort poly *)
Inductive eq@{s;u} (A:Type@{s;u}) (a:A) : A -> Prop := refl : eq A a a.

Check eq_refl : eq@{Prop;Set} True = eq@{Type;Set} True.

Record typ@{s;u} : Type@{s;u+1} := mkt { t : Type@{s;u} }.

Monomorphic Universe u.
Fail Check fun (x:typ@{Prop;Set}) => x : typ@{Type;u}.
Fail Check fun (x:typ@{Type;Set}) => x : typ@{Prop;u}.

Fail Check fun x:typ@{SProp;Set} => x : typ@{Prop;Set}.

Inductive E@{s;} : Prop := .

Fail Check fun x:E@{SProp;} => x:E@{Prop;}.
Check fun x:E@{Prop;} => x:E@{Type;}.

Module Type Covariant.
  Inductive foo@{+s;+u} : Set := .
End Covariant.

Module Invariant.
  Inductive foo@{=s;=u} : Set := .
End Invariant.

Fail Module Invariant' : Covariant := Invariant.

Module Irrelevant.
  Inductive foo@{*s;*u} : Set := .
End Irrelevant.

Module Irrelevant' : Covariant := Irrelevant.

Fail Inductive Box@{+s;l} (A : Type@{l}) : Type@{s;l} := box : A -> Box A.
Inductive Box@{s;l} (A : Type@{l}) : Type@{s;l} := box : A -> Box A.

(* would be inconsistent! *)
Fail Definition unbox (x : Box@{Prop;Type} Type) :=
  match (x : Box@{Type;Type} Type) return Type with box _ A => A end.
