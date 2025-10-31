(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

From Corelib Require Export BinNums PosDef.

(********************************************************)
(** * Binary natural numbers, definitions of operations *)
(********************************************************)

Module N.

(** ** Successor *)

Definition succ n :=
  match n with
  | N0 => Npos xH
  | Npos p => Npos (Pos.succ p)
  end.

(** ** Addition *)

Definition add n m :=
  match n, m with
  | N0, _ => m
  | _, N0 => n
  | Npos p, Npos q => Npos (Pos.add p q)
  end.

(** ** Operation [x -> 2*x+1] *)

Definition succ_double x :=
  match x with
  | N0 => Npos 1
  | Npos p => Npos p~1
  end.

(** ** Operation [x -> 2*x] *)

Definition double n :=
  match n with
  | N0 => N0
  | Npos p => Npos p~0
  end.

(** ** The successor of a [N] can be seen as a [positive] *)

Definition succ_pos (n : N) : positive :=
 match n with
   | N0 => xH
   | Npos p => Pos.succ p
 end.

(** Subtraction *)

Definition sub n m :=
match n, m with
| N0, _ => N0
| n, N0 => n
| Npos n', Npos m' =>
  match Pos.sub_mask n' m' with
  | Pos.IsPos p => Npos p
  | _ => N0
  end
end.

(** Multiplication *)

Definition mul n m :=
  match n, m with
  | N0, _ => N0
  | _, N0 => N0
  | Npos p, Npos q => Npos (Pos.mul p q)
  end.

(** Order *)

Definition compare n m :=
  match n, m with
  | N0, N0 => Eq
  | N0, Npos m' => Lt
  | Npos n', N0 => Gt
  | Npos n', Npos m' => Pos.compare n' m'
  end.

(** Boolean equality and comparison *)

Definition eqb n m :=
  match n, m with
    | N0, N0 => true
    | Npos p, Npos q => Pos.eqb p q
    | _, _ => false
  end.

Definition leb x y :=
 match compare x y with Gt => false | _ => true end.

(** Euclidean division *)

Fixpoint pos_div_eucl (a:positive)(b:N) : N * N :=
  match a with
    | xH =>
       match b with Npos 1 => (Npos 1, N0) | _ => (N0, Npos 1) end
    | xO a' =>
       let (q, r) := pos_div_eucl a' b in
       let r' := double r in
       if leb b r' then (succ_double q, sub r' b)
        else (double q, r')
    | xI a' =>
       let (q, r) := pos_div_eucl a' b in
       let r' := succ_double r in
       if leb b r' then (succ_double q, sub r' b)
        else  (double q, r')
  end.

(** Operation over bits of a [N] number. *)

(** Logical [or] *)

Definition lor n m :=
 match n, m with
   | N0, _ => m
   | _, N0 => n
   | Npos p, Npos q => Npos (Pos.lor p q)
 end.

(** Logical [and] *)

Definition land n m :=
 match n, m with
  | N0, _ => N0
  | _, N0 => N0
  | Npos p, Npos q => Pos.land p q
 end.

(** Logical [diff] *)

Definition ldiff n m :=
 match n, m with
  | N0, _ => N0
  | _, N0 => n
  | Npos p, Npos q => Pos.ldiff p q
 end.

(** [xor] *)

Definition lxor n m :=
  match n, m with
    | N0, _ => m
    | _, N0 => n
    | Npos p, Npos q => Pos.lxor p q
  end.

(** Translation from [N] to [nat] and back. *)

Definition to_nat (a : N) :=
  match a with
    | N0 => O
    | Npos p => Pos.to_nat p
  end.

(** Conversion with a decimal representation for printing/parsing *)

Definition of_uint (d:Decimal.uint) := Pos.of_uint d.

Definition of_hex_uint (d:Hexadecimal.uint) := Pos.of_hex_uint d.

Definition of_num_uint (d:Number.uint) :=
  match d with
  | Number.UIntDecimal d => of_uint d
  | Number.UIntHexadecimal d => of_hex_uint d
  end.

End N.
