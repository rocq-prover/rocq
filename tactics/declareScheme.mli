(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names

module Key : sig

  type t = (string list * UnivGen.QualityOrSet.t option * bool)

  val equal : t -> t -> bool

  module Set : CSet.ExtS with type elt = t
  module Map : CMap.ExtS with type key = t and module Set := Set
end


val declare_scheme : Libobject.locality -> Key.t -> (inductive * GlobRef.t) -> unit
val lookup_scheme : (string list * UnivGen.QualityOrSet.t option * bool) -> inductive -> GlobRef.t
val all_schemes : unit -> GlobRef.t Key.Map.t Indmap_env.t
