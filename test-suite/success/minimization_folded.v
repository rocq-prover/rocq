(* Minimization and variance inference: principality of the types of definitions, number of
   quantified universes, variances reflecting the unfolding, and algebraic universes only in
   covariant positions. Without [Universe Minimization Compat]. *)

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
Set Primitive Projections.
Unset Universe Minimization ToSet.

Module Principality.
  (* An invariant universe of the type, only bounded from below, is kept: [Endo@{u}] is not
     below [Endo@{v}] for [u < v]. *)
  Record Endo@{u} := { car : Type@{u} -> Type@{u} }.
  Definition mk (A : Type) (B : Type) : Endo := {| car := fun X => (A * B * X)%type |}.
  Check mk@{_ _ _}.

  (* A covariant one is set to its lower bound, even an algebraic one. *)
  Definition mkc (A : Type) (B : Type) := (A * B)%type.
  Check mkc@{_ _}.
End Principality.

Module ProjectionsUnfolded.
  (* The variance of a universe of the record argument of a projection is the one of the projected
     field, as conversion unfolds projections first: [Hom (isgraph_0gpd@{u v}) X Y] is
     [Morph@{u v} X Y], whose universes only occur in the types of its parameters. *)
  Class IsGraph@{a h} (A : Type@{a}) := { Hom : A -> A -> Type@{h} }.
  Arguments Hom {A _} _ _.
  Notation "x $-> y" := (Hom x y) (at level 99).
  Record ZeroGpd@{u v} := { carrier :> Type@{u}; rel : carrier -> carrier -> Type@{v} }.
  Record Morph@{u v} (X Y : ZeroGpd@{u v}) := { fn : X -> Y }.
  #[export] Instance isgraph_0gpd@{u v} : IsGraph ZeroGpd@{u v} := {| Hom := Morph@{u v} |}.

  (* The universes of the category in which the hom is taken are irrelevant, as in the unfolding *)
  Definition hom_same@{a b} (X Y : ZeroGpd@{a b}) := X $-> Y.
  Definition hom_same_cumul@{a b a' b' | a <= a', b <= b'} (X Y : ZeroGpd@{a b})
    (f : hom_same@{a b} X Y) : hom_same@{a' b'} X Y := f.

  (* The copy [ZeroGpd@{w z}] of the universes of [X], made by the cast, is not kept: the type only
     depends on it through the projection. As in HoTT's [cat_prod_corec_inv], [IsProduct]... *)
  Definition hom_copy (X : ZeroGpd) := (X : ZeroGpd) $-> X.
  Check hom_copy@{_ _}.
End ProjectionsUnfolded.

Module TermOnly.
  (* A universe of the body only, not of the type, is set to its lower bound whatever its
     variances in the body: the type does not depend on it, while each use would copy it. Here
     the copy [u >= a] of the universe of [A], compared invariantly in [@eq_refl Type@{u} A]. *)
  Definition eq_copy@{a +} (A : Type@{a}) (x : A) : A := let e := @eq_refl Type (A : Type) in x.
  Check eq_copy@{_}.
End TermOnly.

Module AlgebraicOnlyCovariant.
  (* A universe is only set to an algebraic lower bound ([max(i, v)]) where the types of the folded
     subterms in which it occurs are covariant in it: unification copies such subterms into
     holes. Here [s], the relation universe of [Pi_Setoid@{i a v s} S : Setoid@{_ s} _] for a
     non-cumulative [Setoid], is kept in the statement of [pi_refl]. *)
  #[universes(cumulative=no)]
  Class Setoid@{a v} (A : Type@{a}) := { equiv : A -> A -> Type@{v} }.
  Arguments equiv {A _} _ _.

  Definition Pi_Setoid@{i a v s | max(i, v) <= s} {I : Type@{i}} {F : I -> Type@{a}}
    (S : forall i, Setoid@{a v} (F i)) : Setoid@{max(i,a) s} (forall i, F i) :=
    {| equiv f g := forall i, equiv (f i) (g i) |}.

  Lemma pi_refl {I : Type} {F : I -> Type} (S : forall i, Setoid (F i)) (f : forall i, F i)
    (H : forall i, equiv (f i) (f i)) : @equiv _ (Pi_Setoid S) f f.
  Proof. exact H. Qed.
  Check pi_refl@{_ _ _ _}.

  Record PtSetoid@{a w} := { pcar : Type@{a}; pset : Setoid@{a w} pcar; ppt : pcar; prefl : @equiv _ pset ppt ppt }.

  (* The setoid, left to unification, is copied from the type of [pi_refl]: with [s := max(i, v)],
     [w] would have to be equal to [max(i, v)] (as in category-theory's [Fun]). *)
  Definition mk@{i a v w | max(i, v) <= w} {I : Type@{i}} {F : I -> Type@{a}} (S : forall i, Setoid@{a v} (F i))
    (f : forall i, F i) (H : forall i, equiv (f i) (f i)) : PtSetoid@{max(i,a) w} :=
    {| pcar := forall i, F i; pset := _; ppt := f; prefl := pi_refl S f H |}.

  (* In a covariant position, the algebraic lower bound is fine: [Proper]-like statements keep no
     universe for it. *)
  Definition Rel@{a r} (A : Type@{a}) := A -> A -> Type@{r}.
  Definition pw@{i a r} {I : Type@{i}} {F : I -> Type@{a}} (R : forall i, Rel@{a r} (F i)) : Rel (forall i, F i) :=
    fun f g => forall i, R i (f i) (g i).
  Check pw@{_ _ _}.
End AlgebraicOnlyCovariant.

Module SetOnlyCovariant.
  (* Nor to [Set] where the types of the folded subterms of its type are not covariant, even when
     the universe is irrelevant in the declaration: [Q@{u} D@{u}] is the same type for every [u],
     as [D] does not depend on [u], but the type [C@{u}] of [D@{u}] is invariant in [u]. With
     [f : Q@{Set} D@{Set}], the unification of the arguments of [comb] would copy [D@{Set}] into
     the holes [c] and [d], which then cannot hold [D@{v}]. *)
  Record C@{u} := { x : nat; h := Type@{u} }.
  Definition D@{u} : C@{u} := {| x := 0 |}.
  Record Q@{u} (c : C@{u}) := { q : nat }.
  Definition f : Q D := {| q := 0 |}.
  Check f@{_}.
  Definition comb@{u} (c d : C@{u}) (a : Q c) (b : Q d) := a.
  Definition use@{v|} (a : Q@{v} D@{v}) := comb _ _ f a.
End SetOnlyCovariant.

Module TransparentBody.
  (* In a transparent definition, a universe of the body is not set to [Set] when it has folded
     occurrences, whatever their variances: unification and tactics may unfold the definition and
     copy them. In an opaque one, it is, as the body is never unfolded: [k] keeps the universe of
     [D@{u} : C@{u}], [k'] does not. *)
  Record C@{u} := { x : nat; h := Type@{u} }.
  Definition D@{u} : C@{u} := {| x := 0 |}.
  Definition idC@{u} (c : C@{u}) : nat := x c.
  Definition k : nat := idC D.
  Check k@{_}.
  Lemma k' : nat. Proof. exact (idC D). Qed.
  Fail Check k'@{_}.
End TransparentBody.

Module ProjectedRecordInstance.
  (* The projection of a folded record is unfolded by the inference, as conversion does, but
     unification compares the projections of two instances of the record first-order: [hom K@{u o}]
     and [hom K@{u' o'}] give [o = o'] when [o] is flexible, though the field [hom] does not depend
     on [o]. So [o] is not set to [Set] in [l], which would then fix the universe of the objects of
     [K] for every statement unified with its type. *)
  Record Cat@{u} := { ob : Type@{u}; hom : Type@{u} }.
  Definition K@{u o | o < u} : Cat@{u} := {| ob := Type@{o}; hom := nat |}.
  Lemma l : hom K -> hom K.
  Proof. exact (fun x => x). Qed.
  Check l@{_}.
End ProjectedRecordInstance.

Module AxiomTypeOnly.
  (* The minimization of the type of an axiom is the only one: it does not defer the bounds
     mentioning the universes of its binders, here [max(a,p)] for those of [IsEquiv], to a later
     minimization with complete information, which would leave them unbound. *)
  Cumulative Inductive paths@{i} {A : Type@{i}} (a : A) : A -> Type@{i} := idpath : paths a a.
  Definition apD10@{a p} {A : Type@{a}} {P : A -> Type@{p}} {f g : forall x, P x}
    (h : paths f g) : forall x, paths (f x) (g x) :=
    fun x => match h with idpath _ => idpath _ end.
  Record IsEquiv@{a b} {A : Type@{a}} {B : Type@{b}} (f : A -> B) := { inv : B -> A }.
  Axiom isequiv_apD10@{a p} : forall (A : Type@{a}) (P : A -> Type@{p}) f g,
    IsEquiv (@apD10 A P f g).
  Check isequiv_apD10@{_ _}.
End AxiomTypeOnly.
