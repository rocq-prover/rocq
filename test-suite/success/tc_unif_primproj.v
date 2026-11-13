(* Typeclass resolution goes through the unification of tactics, which infers
   canonical structures and unfolds one side or the other. Unfolding the
   projection of a primitive record must leave the other side a chance to be
   unfolded, as unfolding the projection of a non primitive record does:
   otherwise [?F] below is instantiated with the normal form of [nbhs r], for
   which there is no [Filter] instance. *)

Set Primitive Projections.

Definition set T := T -> Prop.
Definition set_system T := set (set T).

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
  Pack U (set_system U) (Class _ _ (IsFiltered U (set_system U) (fun F => F))).

(* A concrete filtered type, built from a factory *)
Parameter R : Type.
Record hasNbhs (T : Type) := HasNbhs { nbhs_of : T -> set_system T }.
Definition nbhs_ball (x : R) : set_system R := fun P => exists y : R, P y /\ P x.
Definition R_factory := HasNbhs R nbhs_ball.
Canonical R_filtered :=
  Pack R R (Class _ _ (IsFiltered R R (nbhs_of _ R_factory))).

Class Filter {T : Type} (F : set_system T) := filterT : F (fun _ => True).

Definition preimage {T U} (f : T -> U) (P : set U) : set T := fun t => P (f t).
Definition fmap {T U : Type} (f : T -> U) (F : set_system T) : set_system U :=
  fun P => nbhs F (preimage f P).

Axiom fmap_filter : forall T U (f : T -> U) (F : set_system T), Filter F -> Filter (fmap f F).
Axiom nbhs_filter : forall x : R, Filter (nbhs x).
#[export] Existing Instance fmap_filter.
#[export] Existing Instance nbhs_filter.

Parameter E : Type.
Parameter inj : R -> E.
Definition e_nbhs (r : R) : set_system E := fun P => nbhs r (fun x => P (inj x)).

(* [e_nbhs r] is [fmap inj (nbhs r)] *)
Goal forall r, Filter (e_nbhs r).
Proof.
  intros r.
  typeclasses eauto.
Qed.
