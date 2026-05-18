(* Conversion must not accept malformed primitive universe instances once
   [__run] / [__unblock] have been pushed to lazy-conversion stack frames. *)

Require Import Corelib.Force Ltac2.Ltac2 Ltac2.Unification.
Set Default Proof Mode "Classic".

Polymorphic Definition one_univ_source@{u} (A : Type@{u}) := A.
Polymorphic Definition two_univ_source@{u v} (A : Type@{u}) (B : Type@{v}) := A.

Ltac2 one_inst () :=
  match Constr.Unsafe.kind '(@one_univ_source@{Set}) with
  | Constr.Unsafe.Constant _ u => u
  | _ => Control.throw Assertion_failure
  end.

Ltac2 two_inst () :=
  match Constr.Unsafe.kind '(@two_univ_source@{Set Set}) with
  | Constr.Unsafe.Constant _ u => u
  | _ => Control.throw Assertion_failure
  end.

Ltac2 zeta (ty : constr) (rhs : constr) :=
  let binder := Constr.Binder.make (Some @z) ty in
  Constr.Unsafe.make
    (Constr.Unsafe.LetIn binder rhs
      (Constr.Unsafe.make (Constr.Unsafe.Rel 1))).

Axiom b : Blocked nat.

Goal True.
Proof.
  (* [PRun] expects a two-sort universe instance.  Giving it a one-sort
     instance is malformed and must not be convertible to a well-formed run. *)
  Fail ltac2:(
    let bad_run := Constr.Unsafe.make
      (Constr.Unsafe.PRun (one_inst ()) 'nat 'nat 'b '(fun x : nat => x)) in
    let good_run := '(__run nat nat b (fun x : nat => x)) in
    if Unification.conv_full (zeta 'nat bad_run) good_run then ()
    else Control.throw Assertion_failure
  ).

  (* [PUnblock] expects a one-sort universe instance.  Giving it a two-sort
     instance is malformed and must not be convertible to a well-formed unblock. *)
  Fail ltac2:(
    let bad_unblock := Constr.Unsafe.make
      (Constr.Unsafe.PUnblock (two_inst ()) 'nat 'b) in
    let good_unblock := '(__unblock nat b) in
    if Unification.conv_full (zeta 'nat bad_unblock) good_unblock then ()
    else Control.throw Assertion_failure
  ).

  exact I.
Qed.
