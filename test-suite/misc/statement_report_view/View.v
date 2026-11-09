(* The public interface has a safe opaque [f], while [Impl.boom]'s proof needs
   the unguarded implementation [f]. A report must follow references from an
   implementation body in its implementation view. *)

Definition no_cycle (n : nat) (h : S n = n) : False.
  induction n as [| n ih].
  - discriminate h.
  - apply ih.
    injection h as h'.
    exact h'.
Defined.

Module Type SIG.
  Lemma f : nat -> nat -> nat.
  Proof. exact (fun _ _ => O). Qed.
  Parameter boom : False.
End SIG.

Module Impl : SIG.
  #[bypass_check(guard)]
  Fixpoint f (n : nat) {struct n} : nat -> nat := fun x => S (f x x).

  Definition step (x : nat) : S (f x x) = f O x :=
    @eq_refl nat (S (f x x)).

  Definition boom : False := no_cycle (f O O) (step O).
End Impl.

(* A transparent Include alias is a path to [A.ax], not another axiom. *)
Module A.
  Axiom ax : nat.
  Definition p : nat := ax.
End A.
Module B.
  Include A.
End B.
Definition alias_model : nat := B.p.

(* A module alias must preserve strengthening: C.p is a transparent edge to
   A.p, never a second axiom. *)
Module C := A.
Definition alias_module_model : nat := C.p.

(* The same alias in an implementation body must still forward to A.ax. *)
Module Type AliasSig.
  Parameter out : nat.
End AliasSig.
Module AliasM : AliasSig.
  Definition out : nat := (fun _ : nat => C.ax) A.ax.
End AliasM.
Definition alias_impl_model : nat := AliasM.out.

(* An identity functor alias must strengthen D.ax just like Module C := A. *)
Module Type AX.
  Parameter ax : nat.
End AX.
Module Id (X : AX) := X.
Module D := Id A.
Module FunAlias : AliasSig.
  Definition out : nat := (fun _ : nat => D.ax) A.ax.
End FunAlias.
Definition fun_alias_model : nat := FunAlias.out.

(* An opaque parent module can fail to expose its implementation fields while
   its direct nested module remains in the environment. *)
Module Type FallbackB.
  Parameter f : Prop.
End FallbackB.
Module Type FallbackC.
  Declare Module D : FallbackB.
End FallbackC.
Module FallbackE : FallbackC.
  Module D <: FallbackB.
    Definition f : Prop := True.
  End D.
End FallbackE.
Module FallbackX.
  Definition model : Prop := FallbackE.D.f.
End FallbackX.
