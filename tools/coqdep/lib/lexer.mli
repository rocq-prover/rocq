(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type qualid = string list

type load = Logical of string | Physical of string

type loc = { loc_start : int; loc_end : int }

type coq_token =
  | Require of qualid option * (loc * qualid) list
  | Declare of string list
  | Load of load
  | External of loc * qualid * string

exception Fin_fichier
exception Syntax_error of loc

val coq_action : Lexing.lexbuf -> coq_token
