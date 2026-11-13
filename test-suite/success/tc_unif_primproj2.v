Set Primitive Projections.
(* Typeclass resolution through structure operations: the instance of a meta
   must not be unfolded more than needed. *)

Definition id {A : Type} (x : A) := x.
Definition set T := T -> Prop.
Definition set_system T := set (set T).
Definition mkset {T : Type} : (T -> Prop) -> set T := id.

(* A structure of "filtered types", in the style of Hierarchy Builder: a
   mixin, a class and a packed structure. *)
Record isFiltered (U T : Type) := IsFiltered { nbhs_op : T -> set_system U }.
Record class_of (U T : Type) := Class { mixin : isFiltered U T }.
Record filteredType (U : Type) := Pack { sort : Type; class : class_of U sort }.
Coercion sort : filteredType >-> Sortclass.

Definition nbhs {U} {T : filteredType U} : T -> set_system U :=
  nbhs_op _ _ (mixin _ _ (class _ T)).
Arguments nbhs : simpl never.

(* A filter is a filtered type, by the identity *)
Canonical set_system_filtered U :=
  Pack U (set_system U) (Class _ _ (IsFiltered U (set_system U) id)).

(* A concrete filtered type, built from a factory *)
Parameter R : Type.
Record hasNbhs (T : Type) := HasNbhs { nbhs_of : T -> set_system T }.
Definition filter_from (B : R -> set R) : set_system R := mkset (fun P => exists y : R, forall z, B y z -> P z).
Parameter ball : R -> R -> set R.
Definition nbhs_ball (x : R) : set_system R := filter_from (ball x).
Definition R_factory := HasNbhs R nbhs_ball.
Canonical R_filtered :=
  Pack R R (Class _ _ (IsFiltered R R (nbhs_of _ R_factory))).

Class Filter {T : Type} (F : set_system T) := filterT : F (fun _ => True).

Definition preimage {T U} (f : T -> U) (P : set U) : set T := fun t => P (f t).
Definition fmap {T U : Type} (f : T -> U) (F : set_system T) : set_system U :=
  mkset (fun P => nbhs F (preimage f P)).

Axiom fmap_filter : forall T U (f : T -> U) (F : set_system T), Filter F -> Filter (fmap f F).
(* stated for any structure: an unfolded neighbourhood filter does not match *)
Axiom nbhs_filter : forall (T : filteredType R) (x : T), Filter (nbhs x).
#[export] Existing Instance fmap_filter.
#[export] Existing Instance nbhs_filter.

Parameter E : Type.
Parameter inj : R -> E.
Definition e_nbhs (r : R) : set_system E := mkset (fun P => nbhs r (fun x => P (inj x))).

(* [e_nbhs r] is [fmap inj (nbhs r)] *)
Goal forall r, Filter (e_nbhs r).
Proof.
  intros r.
  Set Typeclasses Debug Verbosity 1.
  typeclasses eauto.
Qed.
