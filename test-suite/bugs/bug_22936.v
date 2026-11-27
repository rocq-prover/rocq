From Corelib Require Import PrimInt63 PrimArray PrimFloat.

Open Scope array_scope.

(* Nested polymorphic array primitives (default / get) may return an
   accumulator even when their own arguments are closed, so enclosing
   primitives must still check the returned value before running no_check_*. *)

Fail Definition bad_default :
  (fun x : int => PrimInt63.eqb (PrimArray.default (PrimArray.make 0%uint63 x)) 0%uint63) = (fun _ => false) :=
  eq_refl (fun _ => false) <<:
    (fun x : int => PrimInt63.eqb (PrimArray.default (PrimArray.make 0%uint63 x)) 0%uint63) = (fun _ => false).

Fail Definition bad_get :
  (fun x : int => PrimInt63.eqb [| x | x |].[0%uint63] 0%uint63) = (fun _ => false) :=
  eq_refl (fun _ => false) <<:
    (fun x : int => PrimInt63.eqb [| x | x |].[0%uint63] 0%uint63) = (fun _ => false).

(* Closed nested array primitives still compute properly. *)
Definition good_default :
  PrimInt63.eqb (PrimArray.default (PrimArray.make 0%uint63 0%uint63)) 0%uint63 = true :=
  eq_refl true <<: PrimInt63.eqb (PrimArray.default (PrimArray.make 0%uint63 0%uint63)) 0%uint63 = true.

Definition good_get :
  PrimInt63.eqb [| 0%uint63 | 0%uint63 |].[0%uint63] 0%uint63 = true :=
  eq_refl true <<: PrimInt63.eqb [| 0%uint63 | 0%uint63 |].[0%uint63] 0%uint63 = true.

(* Mixed non-int primitive checks (array + float) in a nested primitive expression. *)
Definition good_mixed (a : array float) (f : float) : float :=
  a.[0%uint63 <- PrimFloat.add f 1%float].[0%uint63].

Definition good_mixed_closed :
  PrimFloat.Leibniz.eqb (good_mixed [| 0%float | 0%float |] 1%float) 2%float = true :=
  eq_refl true <<:
    PrimFloat.Leibniz.eqb (good_mixed [| 0%float | 0%float |] 1%float) 2%float = true.

Definition good_mixed_open : good_mixed = good_mixed :=
  eq_refl good_mixed <<: good_mixed = good_mixed.
