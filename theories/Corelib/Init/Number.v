(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Decimal or Hexadecimal numbers *)

Require Import Datatypes Decimal Hexadecimal.

Variant uint := UIntDecimal (u:Decimal.uint) | UIntHexadecimal (u:Hexadecimal.uint).

Variant signed_int := IntDecimal (i:Decimal.int) | IntHexadecimal (i:Hexadecimal.int).
Abbreviation int := signed_int.

Variant number := Decimal (d:Decimal.decimal) | Hexadecimal (h:Hexadecimal.hexadecimal).

Scheme Equality for uint.
Scheme Equality for int.
Scheme Equality for number.
Abbreviation int_eq_dec := signed_int_eq_dec.
Abbreviation int_beq := signed_int_beq.
Abbreviation internal_int_dec_lb := internal_signed_int_dec_lb.
Abbreviation internal_int_dec_bl := internal_signed_int_dec_bl.

Register uint as num.num_uint.type.
Register int as num.num_int.type.
Register number as num.number.type.

(** Pseudo-conversion functions used when declaring
    Number Notations on [uint] and [int]. *)

Definition uint_of_uint (i:uint) := i.
Definition int_of_int (i:int) := i.

Definition to_dec_uint (i:uint) := if i is UIntDecimal u then Some u else None.
Definition to_hex_uint (i:uint) :=
  if i is UIntHexadecimal u then Some u else None.

Definition to_dec_int (i:int) := if i is IntDecimal u then Some u else None.
Definition to_hex_int (i:int) := if i is IntHexadecimal u then Some u else None.

Module NumberNotations.
  Export Hexadecimal.NumberNotations.
  Number Notation Hexadecimal.uint to_hex_uint UIntHexadecimal : hex_uint_scope.
  Number Notation Hexadecimal.int to_hex_int IntHexadecimal : hex_int_scope.

  Export Decimal.NumberNotations.
  Number Notation Decimal.uint to_dec_uint UIntDecimal : dec_uint_scope.
  Number Notation Decimal.int to_dec_int IntDecimal : dec_int_scope.

  Declare Scope num_uint_scope.
  Delimit Scope num_uint_scope with uint.
  Bind Scope num_uint_scope with uint.
  Number Notation uint uint_of_uint uint_of_uint : num_uint_scope.
  Declare Scope num_int_scope.
  Delimit Scope num_int_scope with int.
  Bind Scope num_int_scope with int.
  Number Notation int int_of_int int_of_int : num_int_scope.
End NumberNotations.
