
(* Traversing Subterm Analysis *)

Module Subterm.

  Unset Guard Checking Option Traversing Subterm Analysis.

  (* Rec call on variables are still allowed *)
  Inductive lnat :=
  | lO : lnat
  | lS : lnat -> lnat.

  Fixpoint zero (n : lnat) : lnat :=
    match n with
    | lO => lO
    | lS x => zero x
    end.

  (* Same for Primtive Projections  *)
  Set Primitive Projections.

  Inductive RNat := {
    Rb : bool;
    RNatS : Rb = true -> RNat
  }.

  Fixpoint toNat (x : RNat) : nat :=
    match x.(Rb) as y return x.(Rb) = y -> nat with
    | false => fun e => 0
    | true => fun e => S (toNat (x.(RNatS) e))
    end eq_refl.

  (* subterm analysis going through fixpoint and match are now rejected *)
  Fail Fixpoint foo n k {struct n} : nat :=
    match n with
    | 0 => 0
    | S m => foo (m - k) k
    end.

  (* Whd is still on though *)
  Fixpoint id (n : nat) : nat :=
    match n with
    | 0 => 0
    | S n => S (id ((fun x => x) n))
    end.

  (* [Unset Guard Checking] Keep the Options as is *)
  Unset Guard Checking.
  Set Guard Checking.
  Fail Fixpoint foo n k {struct n} : nat :=
    match n with
    | 0 => 0
    | S m => foo (m - k) k
    end.

  (* Accepted if the analysis is activated *)
  Set Guard Checking Option Traversing Subterm Analysis.

  Fixpoint foo n k {struct n} : nat :=
    match n with
    | 0 => 0
    | S m => foo (m - k) k
    end.

End Subterm.
