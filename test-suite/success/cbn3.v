(* Regression tests for the closure-based cbn implementation. *)

From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
Set Universe Polymorphism.

Ltac2 check_lhs_evar_arg0_is_zero () :=
  let g := Control.goal () in
  match Constr.Unsafe.kind g with
  | Constr.Unsafe.App _ args =>
    let lhs := Array.get args 1 in
    match Constr.Unsafe.kind lhs with
    | Constr.Unsafe.Evar _ eargs =>
      if Int.equal (Array.length eargs) 0 then Control.throw Assertion_failure
      else if Constr.equal (Array.get eargs 0) '0 then ()
      else Control.throw Assertion_failure
    | _ => Control.throw Assertion_failure
    end
  | _ => Control.throw Assertion_failure
  end.

Section UnderBinders.

  (* [norm_cbn] must keep the real local environment when it descends below
     products/lambdas.  In particular, reductions below the binder should see
     a well-formed context, not dummy [Prop] assumptions. *)
  Goal forall (A : Type) (x : A), (fun y : A => y) x = x.
  Proof.
    cbn.
    lazymatch goal with |- forall (A : Type) (x : A), x = x => idtac end.
    reflexivity.
  Qed.

  (* Same issue for local definitions under binders. *)
  Goal forall (A : Type) (x : A), (let y := (fun z : A => z) x in y) = x.
  Proof.
    cbn.
    lazymatch goal with |- forall (A : Type) (x : A), x = x => idtac end.
    reflexivity.
  Qed.

End UnderBinders.

Section CasesAndFixpoints.

  Inductive dep : nat -> Type :=
  | dep0 : dep 0
  | depS : forall n, dep n -> dep (S n).

  (* [norm_cbn] also descends through case predicates and branches.  This used
     to rely on the full annotated case context. *)
  Goal forall n (d : dep n),
      match d in dep n return dep n with
      | dep0 => dep0
      | depS n d => depS n d
      end = d.
  Proof.
    cbn.
    intros [] []; reflexivity.
  Qed.

  (* Recursive bodies are normalized in a context containing the actual
     recursive types, not anonymous dummy assumptions. *)
  Goal forall (A : Type) (x : A),
      (fix go n :=
         match n with
         | 0 => x
         | S n => go n
         end) 2 = x.
  Proof.
    cbn.
    reflexivity.
  Qed.

End CasesAndFixpoints.

Section EvarInstances.

  (* When strong cbn normalizes an evar occurrence, skipped/default evar
     instance entries must be normalized too.  The open term below creates an
     evar under a local let; cbn contracts the let and must update the evar
     instance accordingly. *)
  Goal True.
  Proof.
    let T := open_constr:((let x := (fun y : nat => y) 0 in _ = 0)) in
    enough T by exact I.
    cbn.
    ltac2:(check_lhs_evar_arg0_is_zero ()).
    exact eq_refl.
  Qed.

  (* Same check under ordinary binders, to exercise evar instances while the
     reducer is threading a non-empty local environment. *)
  Goal True.
  Proof.
    let T := open_constr:(((fun (A : Type) (x : A) => (fun y : A => y) _ = x) nat 0)) in
    enough T by exact I.
    cbn.
    ltac2:(check_lhs_evar_arg0_is_zero ()).
    instantiate (1 := x).
    exact eq_refl.
  Qed.

End EvarInstances.
