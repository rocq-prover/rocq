From Corelib Require Import PrimInt63 PrimArray ArrayAxioms.
From Ltac2 Require Import Ltac2.

Ltac2 big_array (n : int) :=
  let small := '[| true | true : bool |] in
  match Constr.Unsafe.kind small with
  | Constr.Unsafe.Array u _ def ty =>
    Constr.Unsafe.make (Constr.Unsafe.Array u (Array.make n 'true) def ty)
  | _ => Control.throw Not_found
  end.

Fail Definition big : array bool := ltac2:(let c := big_array 4194304 in exact $c).

(* Set Default Proof Mode "Classic". *)

(* (* lazy kernel conversion *) *)
(* Definition len_lazy : PrimArray.length big = 4194303%uint63 := eq_refl. *)
(* (* VM conversion *) *)
(* Definition len_vm : PrimArray.length big = 4194304%uint63 := *)
(*   (eq_refl 4194304%uint63 <: PrimArray.length big = 4194304%uint63). *)

(* Lemma bad_noaxiom : False. *)
(* Proof. *)
(*   pose proof (eq_trans (eq_sym len_lazy) len_vm) as H. *)
(*   pose proof (f_equal (fun x => PrimInt63.eqb x 4194303%uint63) H) as H2. *)
(*   vm_compute in H2. discriminate H2. *)
(* Qed. *)
(* Print Assumptions bad_noaxiom. *)
