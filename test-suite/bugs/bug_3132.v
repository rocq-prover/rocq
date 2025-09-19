Unset Elimination Schemes.
Inductive eq (A:Type) (x:A) : A -> Prop :=
    eq_refl : x = x :>A

where "x = y :> A" := (@ eq A x y) : type_scope.

Notation "x = y" := (x = y :>_) : type_scope.
Notation "x <> y  :> T" := (~ x = y :>T) : type_scope.
Notation "x <> y" := (x <> y :>_) : type_scope.

Arguments eq {A} x _.
Arguments eq_refl {A x} , [A] x.
Set Elimination Schemes.

Scheme eq_rect := Minimality for eq Sort Type.
Scheme eq_rec := Minimality for eq Sort Set.
Scheme eq_ind := Minimality for eq Sort Prop.

(* needed for discriminate to recognize the hypothesis *)
Register eq as core.eq.type.
Register eq_refl as core.eq.refl.
Register eq_ind as core.eq.ind.
Register eq_rect as core.eq.rect.

#[universes(polymorphic=yes)]
Instance eq_Has_Leibniz_elim@{s ; l l'} : Has_Leibniz@{Type Prop s;l Set l'} (@eq) :=
  fun A x P t y e => match e with eq_refl => t end.

Lemma foo (H : true = false) : False.
Proof.
  discriminate.
Defined.
Print foo.

Goal False.
  let c := eval cbv delta [foo] in foo in
    match c with
      context[eq_Has_Leibniz_elim] => idtac
    end.
Abort.
