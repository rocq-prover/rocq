(* Regression test for #21733: universe constraints dropped by abstract
   when proof term references hypotheses via Var nodes whose types
   contain universe levels not directly present in the body/type. *)
Require Ltac2.Ltac2.
#[export] Set Universe Polymorphism.
#[export] Set Implicit Arguments.

Inductive eq@{s;u} {A:Type@{s;u}} (a:A) : A -> SProp := eq_refl : eq a a.
#[local] Notation "x = y" := (eq x y) : type_scope.

Record Iso@{s s';u u'} (A : Type@{s;u}) (B : Type@{s';u'}) := {
    to :> A -> B;
    from : B -> A;
    to_from : forall x, to (from x) = x;
    from_to : forall x, from (to x) = x;
}.
Record > rel_iso@{s s';u u'} {A B} (i : Iso@{s s';u u'} A B) (x : A) (y : B) : SProp := { proj_rel_iso :> i.(to) x = y }.

Export Ltac2.Notations.

Record Producer (G : Type -> Type) := { semProdSize : forall (A : Type), G A -> SProp }.

Ltac2 refine_preterm use_gc h :=
  let fl := Constr.Pretype.Flags.open_constr_flags_no_tc in
  unshelve (
    let c :=
      if use_gc then
        Constr.Pretype.pretype fl (Constr.Pretype.expected_oftype (Control.goal ())) h
      else (
        let c := Constr.Pretype.pretype fl Constr.Pretype.expected_without_type_constraint h in
        let ty := Constr.type c in
        let gl := Control.goal () in
        unify $ty $gl;
        c) in
    cbv beta iota zeta in *;
    let c := eval cbv beta iota zeta in $c in
    eexact $c);
  Control.shelve_unifiable ();
  cbv beta zeta in *.

Ltac2 resolve_iso_assumption () :=
  match! goal with
  | [ h : Iso _ _ |- _ ] => let hv := Control.hyp h in exact $hv
  | [ h : rel_iso _ _ _ |- _ ] => let hv := Control.hyp h in exact $hv
  end.

Ltac2 resolve_rel_iso () :=
  match! goal with
  | [ h : rel_iso _ _ _ |- _ ] => let hv := Control.hyp h in exact $hv
  end.

Ltac2 resolve_functor_iso () :=
  let f := lazy_match! goal with | [ |- Iso ?f _ ] => f end in
  let (_head, args) := Constr.decompose_app_list f in
  let arg := List.nth args 0 in
  let iso_proof :=
    match! goal with
    | [ h : forall (_ _ : Type), Iso _ _ -> Iso _ _ |- _ ] => Control.hyp h
    end in
  let hyp := preterm:($iso_proof
    $arg ltac2:(intros; cbv beta) ltac2:(intros; cbv beta; resolve_iso_assumption ())) in
  refine_preterm Ltac2.Init.false hyp.

Ltac2 inlined_resolve_known_isos use_gc iso_proof :=
  let f := lazy_match! goal with | [ |- Iso ?f _ ] => f end in
  let (_h, args) := Constr.decompose_app_list f in
  let arg1 := List.nth args 0 in
  let arg2 := List.nth args 1 in
  let arg3 := List.nth args 2 in
  let arg4 := List.nth args 3 in
  let hyp := preterm:($iso_proof
    $arg1 ltac2:(intros; cbv beta) ltac2:(intros; cbv beta; resolve_functor_iso ())
    $arg2 ltac2:(intros; cbv beta) ltac2:(intros; cbv beta; resolve_rel_iso ())
    $arg3 ltac2:(intros; cbv beta) ltac2:(intros; cbv beta; resolve_iso_assumption ())
    $arg4 ltac2:(intros; cbv beta) ltac2:(intros; cbv beta; resolve_rel_iso ())) in
  refine_preterm use_gc hyp.

Parameter Producer_iso : forall x1 x2 : Type -> Type, @Iso (Producer x1) (Producer x2).
Parameter semProdSize_iso : forall (x1 x2 : Type -> Type) (hx : forall x3 x4 : Type, @Iso x3 x4 -> @Iso (x1 x3) (x2 x4)) (x3 : Producer x1) (x4 : Producer x2), @rel_iso (Producer x1) (Producer x2) (Producer_iso x1 x2) x3 x4 -> forall (x5 x6 : Type) (hx1 : @Iso x5 x6) (x7 : x1 x5) (x8 : x2 x6), @rel_iso (x1 x5) (x2 x6) (hx x5 x6 hx1) x7 x8 -> @Iso (@semProdSize x1 x3 x5 x7) (@semProdSize x2 x4 x6 x8).

Goal forall (x1 x2 : Type -> Type) (hx : forall x3 x4 : Type, Iso x3 x4 -> Iso (x1 x3) (x2 x4))
  (x3 : Producer x1) (x4 : Producer x2) (H : rel_iso (Producer_iso x1 x2) x3 x4)
  (x5 x6 : Type) (hx1 : Iso x5 x6) (x7 : x1 x5) (x8 : x2 x6) (H0 : rel_iso (hx x5 x6 hx1) x7 x8),
  Iso (semProdSize x3 x7) (semProdSize x4 x8).
Proof.
  intros.
  abstract (ltac2:(inlined_resolve_known_isos Ltac2.Init.false constr:(semProdSize_iso))).
Qed.
