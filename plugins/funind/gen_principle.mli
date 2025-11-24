(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val warn_cannot_define_graph : ?loc:Loc.t -> Pp.t * Pp.t -> unit
val warn_cannot_define_principle : ?loc:Loc.t -> Pp.t * Pp.t -> unit

val do_generate_principle_interactive : Summary.Interp.mut ->
  Vernacexpr.fixpoints_expr -> Declare.Proof.t

val do_generate_principle : Summary.Interp.mut ->
  Vernacexpr.fixpoints_expr -> unit
val make_graph : Summary.Interp.mut ->
  Names.GlobRef.t -> unit

(* Can be thrown by build_{,case}_scheme *)
exception No_graph_found

val build_scheme : Summary.Interp.mut ->
  (Names.lident * Libnames.qualid * UnivGen.QualityOrSet.t) list -> unit
val build_case_scheme : Summary.Interp.mut ->
  Names.lident * Libnames.qualid * UnivGen.QualityOrSet.t -> unit
