(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Ind_tables

(** Induction/recursion schemes *)

val elim_scheme : dep:bool -> to_kind:UnivGen.QualityOrSet.t -> individual scheme_kind

val mutual_rect_dep : mutual scheme_kind
val mutual_rec_dep : mutual scheme_kind
val mutual_ind_dep : mutual scheme_kind
val mutual_sind_dep : mutual scheme_kind
val mutual_rect_nodep : mutual scheme_kind
val mutual_rec_nodep : mutual scheme_kind
val mutual_ind_nodep : mutual scheme_kind
val mutual_sind_nodep : mutual scheme_kind

(** Case analysis schemes *)

val case_dep : individual scheme_kind
val case_nodep : individual scheme_kind
val casep_dep : individual scheme_kind
val casep_nodep : individual scheme_kind

val cases_dep : individual scheme_kind
val cases_nodep : individual scheme_kind
val casep_dep_set : individual scheme_kind
val case_nodep_set : individual scheme_kind

(** Recursor names utilities *)

val lookup_eliminator : Environ.env -> Names.inductive -> UnivGen.QualityOrSet.t -> Names.GlobRef.t
val elimination_suffix : UnivGen.QualityOrSet.t -> string
val make_elimination_ident : Names.Id.t -> UnivGen.QualityOrSet.t -> Names.Id.t
