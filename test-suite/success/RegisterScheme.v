(* use our own eq instead of the corelib one (which has rewriting schemes already declared) *)
Inductive eq (A:Type) (x:A) : A -> Prop :=
    eq_refl : x = x :>A

where "x = y :> A" := (@eq A x y) : type_scope.

Arguments eq {A} x _.
Arguments eq_refl {A x} , [A] x.

Arguments eq_ind [A] x P _ y _ : rename.
Arguments eq_rec [A] x P _ y _ : rename.
Arguments eq_rect [A] x P _ y _ : rename.

Notation "x = y" := (eq x y) : type_scope.
Notation "x <> y  :> T" := (~ x = y :>T) : type_scope.
Notation "x <> y" := (~ (x = y)) : type_scope.

Register eq as core.eq.type.
Register eq_refl as core.eq.refl.
Register eq_ind as core.eq.ind.
Register eq_rect as core.eq.rect.

Set Universe Polymorphism.

Definition paths_rew_r_dep (A : Type) (x y : A) (P : forall y0 : A, y0 = y -> Type)
  (u : P y eq_refl) (H : x = y)
  : P x H.
Proof. destruct H;assumption. Defined.

Module TestLocal.
  Local Register Scheme paths_rew_r_dep as Left2Right Dependent Rewrite for eq.

  Section GenMem.
    Variable A : Type.

    Theorem upd_nop (a : A) (x : A) (e : a = x) (H: e = e)
      : eq_refl a = eq_refl.
    Proof.
      subst.
      exact H.
    Qed.
  End GenMem.
End TestLocal.

Module TestExport.
  #[export] Register Scheme paths_rew_r_dep as Left2Right Dependent Rewrite for eq.

  Section GenMem.
    Variable A : Type.

    Theorem upd_nop (a : A) (x : A) (e : a = x) (H: e = e)
      : eq_refl a = eq_refl.
    Proof.
      subst.
      exact H.
    Qed.
  End GenMem.
End TestExport.

Module Test1.
  Section GenMem.
    Variable A : Type.

    Theorem upd_nop (a : A) (x : A) (e : a = x) (H: e = e)
      : eq_refl a = eq_refl.
    Proof.
      (* neither TestLocal or TestExport registered the scheme *)
      Fail subst.
      Export TestLocal.
      Fail subst.
      Export TestExport.
      subst.
      exact H.
    Qed.
  End GenMem.
End Test1.

Section GenMem.
  Variable A : Type.

  Theorem upd_nop (a : A) (x : A) (e : a = x) (H: e = e)
    : eq_refl a = eq_refl.
  Proof.
    (* Export reverted by section end *)
    Fail subst.
  Abort.
End GenMem.


Module TestGlobal.
  Global Register Scheme paths_rew_r_dep as Left2Right Dependent Rewrite for eq.

  Section GenMem.
    Variable A : Type.

    Theorem upd_nop (a : A) (x : A) (e : a = x) (H: e = e)
      : eq_refl a = eq_refl.
    Proof.
      subst.
      exact H.
    Qed.
  End GenMem.
End TestGlobal.

Section GenMem.
  Variable A : Type.

  Theorem upd_nop (a : A) (x : A) (e : a = x) (H: e = e)
    : eq_refl a = eq_refl.
  Proof.
    subst.
    exact H.
  Qed.
End GenMem.
