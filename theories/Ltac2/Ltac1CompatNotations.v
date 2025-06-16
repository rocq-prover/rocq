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

From Corelib.Init Require Import Ltac Tactics.
From Ltac2 Require Import Init Notations.
From Ltac2 Require Std Control Constr Ltac1.

Ltac2 Notation t1(thunk(self)) "+" t2(thunk(self)) : 2 := Control.plus t1 (fun _ => t2 ()).

(* abstract: in Notations *)

Ltac2 Notation "absurd" c(constr) : 1 := ltac1:(c |- absurd c) (Ltac1.of_constr c).

(* admit, apply, assert: in Notations *)

Ltac2 Type exn ::= [ Succeeded ].

(* XXX drops backtrace *)
Ltac2 assert_succeeds0 (tac:unit -> unit) :=
  Control.orelse (fun () => Control.once tac; Control.zero Succeeded)
    (fun e => match e with Succeeded => () | _ => Control.zero e end).
Ltac2 Notation "assert_succeeds" tac(thunk(tactic(3))) : 1 := assert_succeeds0 tac.

(* XXX could also accept "tac:unit -> 'a", do we want to? *)
Ltac2 assert_fails0 (tac:unit -> unit) :=
  match Control.case tac with
  | Val ((),_) => Control.backtrack_tactic_failure "succeeds"
  | Err _ => ()
  end.
Ltac2 Notation "assert_fails" tac(thunk(tactic(3))) : 1 := assert_fails0 tac.

(* assumption, auto: in Notations *)

Ltac2 Notation "autoapply" c(constr) "with" id(ident) : 1 :=
  ltac1:(c id |- autoapply c with id) (Ltac1.of_constr c) (Ltac1.of_ident id).

(* autorewrite, autounfold, autounfold_one: TODO *)

(* btauto: TODO (or don't) *)

(* case, case_eq: TODO *)

(* cbn, cbv, change: in Notations *)

Ltac2 Notation "change_no_check" c(conversion) cl(opt(clause)) : 1 :=
  let (pat, c) := c in
  Std.change_no_check pat c (default_on_concl cl).

(* classical_left/right: TODO *)

(* clear: in Notations *)

(* clear dependent, clearbody: TODO *)

(* cofix: TODO *)

(* compare: TODO (or don't) *)

(* compute: TODO (or let people use cbv) *)

(* congruence: in Notations *)

Ltac2 Notation "constr_eq" c1(constr) c2(constr) : 1 :=
  ltac1:(c1 c2 |- constr_eq c1 c2) (Ltac1.of_constr c1) (Ltac1.of_constr c2).

Ltac2 Notation "constr_eq_nounivs" c1(constr) c2(constr) : 1 :=
  ltac1:(c1 c2 |- constr_eq_nounivs c1 c2) (Ltac1.of_constr c1) (Ltac1.of_constr c2).

Ltac2 Notation "constr_eq_strict" c1(constr) c2(constr) : 1 :=
  if Constr.equal c1 c2 then ()
  else Control.backtrack_tactic_failure "Not equal".

(* constructor: in Notations *)

(* context: not sure *)

Ltac2 Notation "contradict" id(ident) : 1 := ltac1:(id |- contradict id) (Ltac1.of_ident id).

(* contradiction, convert, cut: TODO *)

(* cycle: in Notations *)

(* TODO:
  debug auto
  debug eauto
  debug trivial
  decide
  decide equality
  decompose
  decompose record
  decompose sum
  dependent destruction
  dependent generalize_eqs
  dependent generalize_eqs_vars
  dependent induction
  dependent inversion
  dependent inversion_clear
  dependent rewrite
  dependent simple inversion
  destauto
*)

(* destruct: in Notations *)

(* dintuition: TODO *)

(* discriminate, do: in Notations *)

(* dtauto: TODO *)

(* e-z: not checked yet *)

Ltac2 Notation "transitivity" c(constr) := Std.transitivity c.
