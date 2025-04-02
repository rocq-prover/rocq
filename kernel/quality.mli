(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** {6 The sort qualities of CCI. } *)

module QGlobal :
sig

  type t

  val make : Names.DirPath.t -> Names.Id.t -> t
  val repr : t -> Names.DirPath.t * Names.Id.t
  val equal : t -> t -> bool
  val hash : t -> int
  val compare : t -> t -> int
  val to_string : t -> string

end

module QVar :
sig
  type t

  val var_index : t -> int option

  val make_var : int -> t
  val make_unif : string -> int -> t
  val make_global : QGlobal.t -> t

  val equal : t -> t -> bool
  val compare : t -> t -> int

  val hash : t -> int
  val hcons : t Hashcons.f

  val raw_pr : t -> Pp.t
  (** Using this is incorrect when names are available, typically from an evar map. *)

  val to_string : t -> string
  (** Debug printing *)

  type repr =
    | Var of int
    | Unif of string * int
    | Global of QGlobal.t

  val repr : t -> repr
  val of_repr : repr -> t

  val is_unif : t -> bool

  module Set : CSig.SetS with type elt = t

  module Map : CMap.ExtS with type key = t and module Set := Set
end

type constant = QProp | QSProp | QType
type t = QVar of QVar.t | QConstant of constant

type quality = t

module Constants : sig
  val equal : constant -> constant -> bool
  val compare : constant -> constant -> int
  val to_string : constant -> string
  val pr : constant -> Pp.t
end

val qprop : t
val qsprop : t
val qtype : t

val var : int -> t
(** [var i] is [QVar (QVar.make_var i)] *)

val global : QGlobal.t -> t
(** [global i] is [QVar (QVar.make_global i)] *)

val var_index : t -> int option

val equal : t -> t -> bool

val is_qsprop : t -> bool
val is_qprop : t -> bool
val is_qtype : t -> bool
val is_qvar : t -> bool
val is_qconst : t -> bool
val is_qglobal : t -> bool
val is_impredicative : t -> bool

val compare : t -> t -> int

val all_constants : t list
val all : t list
(** This provides a list with all qualities, and a dummy QVar. *)

val pr : (QVar.t -> Pp.t) -> t -> Pp.t

val raw_pr : t -> Pp.t

val hash : t -> int

val hcons : t Hashcons.f

(* XXX Inconsistent naming: this one should be subst_fn *)
val subst : (QVar.t -> t) -> t -> t

val subst_fn : t QVar.Map.t -> QVar.t -> t

module Set : CSig.SetS with type elt = t
module Map : CMap.ExtS with type key = t and module Set := Set

type 'q pattern =
  PQVar of 'q | PQConstant of constant

val pattern_match : int option pattern -> t -> ('t, t, 'u) Partial_subst.t -> ('t, t, 'u) Partial_subst.t option

val to_string : t -> string

module ElimConstraint : sig
  type kind = Equal | ElimTo

  val pr_kind : kind -> Pp.t

  type t = quality * kind * quality

  val equal : t -> t -> bool

  val compare : t -> t -> int

  val pr : (QVar.t -> Pp.t) -> t -> Pp.t

  val raw_pr : t -> Pp.t

  val hcons : t Hashcons.f
end

module ElimConstraints : sig
  include Stdlib.Set.S with type elt = ElimConstraint.t
  val pr : (QVar.t -> Pp.t) -> t -> Pp.t

  val hcons : t Hashcons.f
end

module QCumulConstraint : sig
  type kind = Eq | Leq
  type t = quality * kind * quality

  val trivial : t -> bool
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val pr : (QVar.t -> Pp.t) -> t -> Pp.t
  val raw_pr : t -> Pp.t
end

module QCumulConstraints : sig
  include CSig.SetS with type elt = QCumulConstraint.t
  val pr : (QVar.t -> Pp.t) -> t -> Pp.t
  val trivial : t -> bool
end
