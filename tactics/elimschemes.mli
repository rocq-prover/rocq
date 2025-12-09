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
open Names
open Environ

(* -------------------------------------------------------------------------- *)

(** Declare an inductive should be eliminated dependently even though it's in Prop *)
val declare_prop_but_default_dependent_elim : Summary.Interp.mut -> inductive -> unit

(** Check if an inductive should be eliminated dependently even though it's in Prop *)
val is_prop_but_default_dependent_elim : inductive -> bool

(** Returns [QType] if the inductive block can be eliminated dependently,
    the sort of the inductive block otherwise   *)
val pseudo_sort_quality_for_elim : inductive -> Declarations.one_inductive_body -> Sorts.Quality.t

(** Check that an inductive block can be eliminated dependently, and is declared to be so if in Prop *)
val default_case_analysis_dependence : env -> inductive -> bool

(* -------------------------------------------------------------------------- *)

(** Induction/recursion schemes *)
val elim_scheme : dep:bool -> to_kind:UnivGen.QualityOrSet.t -> individual scheme_kind

(** Case analysis schemes *)

val case_dep : individual scheme_kind
val case_nodep : individual scheme_kind
val casep_dep : individual scheme_kind
val casep_nodep : individual scheme_kind

(** Recursor names utilities *)

val lookup_eliminator : Environ.env -> Names.inductive -> UnivGen.QualityOrSet.t -> Names.GlobRef.t
val elimination_suffix : UnivGen.QualityOrSet.t -> string
val make_elimination_ident : Names.Id.t -> UnivGen.QualityOrSet.t -> Names.Id.t
