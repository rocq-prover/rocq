(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)


(* This file contains Ltac2 Notations reproducing Ltac1 parsing of tactics,
   that can be harmful to parsing, and produce bad error messages.
   They should hence only be imported to port proof script written in Ltac1,
   or if they are really wanted.
*)

Require Import Ltac2.Init Ltac2.Std.

Ltac2 Notation "transitivity" c(constr) : 1 := Std.transitivity c.

Ltac2 Notation "rename" renames(list1(seq(ident, "into", ident), ",")) :=
  Std.rename renames.
