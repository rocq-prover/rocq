(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This file defines a lot of different notions of names used pervasively in
    the kernel as well as in other places. The essential datatypes exported by
    this API are:

    - Id.t is the type of identifiers, that is morally a subset of strings which
      only contains Unicode characters of the Letter kind (and a few more).
    - Name.t is an ad-hoc variant of Id.t option allowing to handle optionally
      named objects.
    - DirPath.t represents generic paths as sequences of identifiers.
    - ModPath.t are module paths.
    - KerName.t are absolute names of objects in Rocq.
*)

open Util

(** {6 Identifiers } *)

(** Representation and operations on identifiers. *)
module Id :
sig
  type t
  (** Values of this type represent (Rocq) identifiers. *)

  val equal : t -> t -> bool
  (** Equality over identifiers. *)

  val compare : t -> t -> int
  (** Comparison over identifiers. *)

  val hash : t -> int
  (** Hash over identifiers. *)

  val is_valid : string -> bool
  (** Check that a string may be converted to an identifier. *)

  val is_valid_ident_part : string -> bool
  (** Check that a string is a valid part of an identifier *)

  val of_bytes : bytes -> t
  val of_string : string -> t
  (** Converts a string into an identifier.
      @raise UserError if the string is invalid as an identifier. *)

  val of_string_soft : string -> t
  (** Same as {!of_string} except that any string made of supported UTF-8 characters is accepted.
      @raise UserError if the string is invalid as an UTF-8 string. *)

  val to_string : t -> string
  (** Converts a identifier into an string. *)

  val print : t -> Pp.t
  (** Pretty-printer. *)

  module Set : Set.ExtS with type elt = t
  (** Finite sets of identifiers. *)

  module Map : Map.ExtS with type key = t and module Set := Set
  (** Finite maps of identifiers. *)

  module Pred : Predicate.S with type elt = t
  (** Predicates over identifiers. *)

  module List : List.MonoS with type elt = t
  (** Operations over lists of identifiers. *)

  val hcons : t Hashcons.f
  (** Hashconsing of identifiers. *)

end

(** Representation and operations on identifiers that are allowed to be anonymous
    (i.e. "_" in concrete syntax). *)
module Name :
sig
  type t = Anonymous     (** anonymous identifier *)
         | Name of Id.t  (** non-anonymous identifier *)

  val mk_name : Id.t -> t
  (** constructor *)

  val is_anonymous : t -> bool
  (** Return [true] iff a given name is [Anonymous]. *)

  val is_name : t -> bool
  (** Return [true] iff a given name is [Name _]. *)

  val compare : t -> t -> int
  (** Comparison over names. *)

  val equal : t -> t -> bool
  (** Equality over names. *)

  val hash : t -> int
  (** Hash over names. *)

  val hcons : t Hashcons.f
  (** Hashconsing over names. *)

  val print : t -> Pp.t
  (** Pretty-printer (print "_" for [Anonymous]. *)

end

(** {6 Type aliases} *)

type name = Name.t = Anonymous | Name of Id.t
[@@ocaml.deprecated "(8.8) Use Name.t"]

type variable = Id.t

(** {6 Directory paths = section names paths } *)

module DirPath :
sig
  type t
  (** Type of directory paths. Essentially a list of module identifiers. The
      order is reversed to improve sharing. E.g. A.B.C is ["C";"B";"A"] *)

  val equal : t -> t -> bool
  (** Equality over directory paths. *)

  val compare : t -> t -> int
  (** Comparison over directory paths. *)

  val hash : t -> int
  (** Hash over directory paths. *)

  val make : Id.t list -> t
  (** Create a directory path. (The list must be reversed). *)

  val repr : t -> Id.t list
  (** Represent a directory path. (The result list is reversed). *)

  val empty : t
  (** The empty directory path. *)

  val is_empty : t -> bool
  (** Test whether a directory path is empty. *)

  val dummy : t
  (** Used in [Safe_typing.empty_environment] and similar *)

  val hcons : t Hashcons.f
  (** Hashconsing of directory paths. *)

  val to_string : t -> string
  (** Print non-empty directory paths as ["root.module.submodule"] *)

  val print : t -> Pp.t

  module Set : Set.ExtS with type elt = t
  module Map : Map.ExtS with type key = t and module Set := Set
end

module DPset = DirPath.Set [@@deprecated "(9.2) Use DirPath.Set"]
module DPmap = DirPath.Map [@@deprecated "(9.2) Use DirPath.Map"]

(** {6 Unique names for bound modules} *)

module MBId :
sig
  type t
  (** Unique names for bound modules. Each call to [make] constructs a fresh
      unique identifier. *)

  val equal : t -> t -> bool
  (** Equality over unique bound names. *)

  val compare : t -> t -> int
  (** Comparison over unique bound names. *)

  val hash : t -> int
  (** Hash over unique bound names. *)

  val make : DirPath.t -> Id.t -> t
  (** The first argument is a file name, to prevent conflict between different
      files. *)

  val repr : t -> int * Id.t * DirPath.t
  (** Reverse of [make]. *)

  val to_id : t -> Id.t
  (** Return the identifier contained in the argument. *)

  val to_string : t -> string
  (** Encode as a string (not to be used for user-facing messages). *)

  val debug_to_string : t -> string
  (** Same as [to_string], but outputs extra information related to debug. *)

  module Set : Set.ExtS with type elt = t
  module Map : Map.ExtS with type key = t and module Set := Set

end

module MBIset = MBId.Set [@@deprecated "(9.2) Use MBId.Set"]
module MBImap = MBId.Map [@@deprecated "(9.2) Use MBId.Map"]

(** {6 The module part of the kernel name } *)

module ModPath :
sig
  type t =
    | MPfile of DirPath.t
    | MPbound of MBId.t
    | MPdot of t * Id.t

  val compare : t -> t -> int
  val equal : t -> t -> bool
  val hash : t -> int

  val subpath : t -> t -> bool
  (* [subpath p q] is true when q = p.l1. ... . ln, where n is potentially 0 *)

  val is_bound : t -> bool

  val dummy : t
  (** ([= MPfile DirPath.dummy]) *)

  val dp : t -> DirPath.t

  val to_string : t -> string
  (** Converts a identifier into an string. *)

  val print : t -> Pp.t
  (** Pretty-printer. *)

  val debug_to_string : t -> string
  (** Same as [to_string], but outputs extra information related to debug. *)

  module Set : Set.ExtS with type elt = t
  module Map : Map.ExtS with type key = t and module Set := Set

end

module MPset = ModPath.Set [@@deprecated "(9.2) Use ModPath.Set"]
module MPmap = ModPath.Map [@@deprecated "(9.2) Use ModPath.Map"]

(** {6 The absolute names of objects seen by kernel } *)

module KerName :
sig
  type t

  (** Constructor and destructor *)
  val make : ModPath.t -> Id.t -> t
  val repr : t -> ModPath.t * Id.t

  (** Projections *)
  val modpath : t -> ModPath.t
  val label : t -> Id.t

  val to_string : t -> string
  (** Encode as a string (not to be used for user-facing messages). *)

  val print : t -> Pp.t
  (** Print internal representation (not to be used for user-facing messages). *)

  val debug_to_string : t -> string
  (** Same as [to_string], but outputs extra information related to debug. *)

  val debug_print : t -> Pp.t
  (** Same as [print], but outputs extra information related to debug. *)

  (** Comparisons *)
  val compare : t -> t -> int
  val equal : t -> t -> bool
  val hash : t -> int

  module Set : CSig.USetS with type elt = t
  module Map : Map.UExtS with type key = t and module Set := Set
  module Pred : Predicate.S with type elt = t

end

module KNset = KerName.Set [@@deprecated "(9.2) Use KerName.Set"]
module KNpred = KerName.Pred [@@deprecated "(9.2) Use KerName.Pred"]
module KNmap = KerName.Map [@@deprecated "(9.2) Use KerName.Map"]

(** {6 Signature for quotiented names} *)

module type EqType =
sig
  type t
  val compare : t -> t -> int
  val equal : t -> t -> bool
  val hash : t -> int
end

module type QNameS =
sig
  type t
  (** A type of reference that implements an implicit quotient by containing
      two different names. The first one is the user name, i.e. what the user
      sees when printing. The second one is the canonical name, which is the
      actual absolute name of the reference.

      This mechanism is fundamentally tied to the module system of Rocq. Functor
      application and module inclusion are the typical ways to introduce names
      where the canonical and user components differ. In particular, the two
      components should be undistinguishable from the point of view of typing,
      i.e. from a "kernel" ground. This aliasing only makes sense inside an
      environment, but at this point this notion is not even defined so, this
      dual name trick is fragile. One has to ensure many invariants when
      creating such names, but the kernel is quite lenient when it comes to
      checking that these invariants hold. (Read: there are soundness bugs
      lurking in the module system.)

      One could enforce the invariants by splitting the names and storing that
      information in the environment instead, but unfortunately, this wreaks
      havoc in the upper layers. The latter are infamously not stable by
      syntactic equality, in particular they might observe the difference
      between canonical and user names if not packed together.

      For this reason, it is discouraged to use the canonical-accessing API
      in the upper layers, notably the [CanOrd] module below. Instead, one
      should use their quotiented versions defined in the [Environ] module.
      Eventually all uses to [CanOrd] outside of the kernel should be removed.

      CAVEAT: name sets and maps are still exposing a canonical-accessing API
      surreptitiously. *)

  module CanOrd : EqType with type t = t
  (** Equality functions over the canonical name. Their use should be
      restricted to the kernel. *)

  module UserOrd : EqType with type t = t
  (** Equality functions over the user name. *)

  val canonize : t -> t
  (** Returns the canonical version of the name *)
end

(** {6 Constant Names } *)

module Constant:
sig
  type t

  (** Constructors *)

  val make : KerName.t -> KerName.t -> t
  (** Builds a constant name from a user and a canonical kernel name. *)

  val make1 : KerName.t -> t
  (** Special case of [make] where the user name is canonical.  *)

  val make2 : ModPath.t -> Id.t -> t
  (** Shortcut for [(make1 (KerName.make ...))] *)

  (** Projections *)

  val user : t -> KerName.t
  val canonical : t -> KerName.t

  val modpath : t -> ModPath.t
  (** Shortcut for [KerName.modpath (user ...)] *)

  val label : t -> Id.t
  (** Shortcut for [KerName.label (user ...)] *)

  (** Comparisons *)

  include QNameS with type t := t

  val change_label : t -> Id.t -> t
  (** Builds a new constant name with a different label *)

  (** Displaying *)

  val to_string : t -> string
  (** Encode as a string (not to be used for user-facing messages). *)

  val print : t -> Pp.t
  (** Print internal representation (not to be used for user-facing messages). *)

  val debug_to_string : t -> string
  (** Same as [to_string], but outputs extra information related to debug. *)

  val debug_print : t -> Pp.t
  (** Same as [print], but outputs extra information related to debug. *)

end

(** The [*_env] modules consider an order on user part of names
   the others consider an order on canonical part of names*)
module Cpred : Predicate.S with type elt = Constant.t
module Cset : CSig.USetS with type elt = Constant.t
module Cset_env  : CSig.USetS with type elt = Constant.t

module Cmap : Map.UExtS with type key = Constant.t and module Set := Cset
(** A map whose keys are constants (values of the {!Constant.t} type).
    Keys are ordered wrt. "canonical form" of the constant. *)

module Cmap_env : Map.UExtS with type key = Constant.t and module Set := Cset_env
(** A map whose keys are constants (values of the {!Constant.t} type).
    Keys are ordered wrt. "user form" of the constant. *)

(** {6 Inductive names} *)

module MutInd :
sig
  type t

  (** Constructors *)

  val make : KerName.t -> KerName.t -> t
  (** Builds a mutual inductive name from a user and a canonical kernel name. *)

  val make1 : KerName.t -> t
  (** Special case of [make] where the user name is canonical.  *)

  val make2 : ModPath.t -> Id.t -> t
  (** Shortcut for [(make1 (KerName.make ...))] *)

  (** Projections *)

  val user : t -> KerName.t
  val canonical : t -> KerName.t

  val modpath : t -> ModPath.t
  (** Shortcut for [KerName.modpath (user ...)] *)

  val label : t -> Id.t
  (** Shortcut for [KerName.label (user ...)] *)

  (** Comparisons *)

  include QNameS with type t := t

  (** Displaying *)

  val to_string : t -> string
  (** Encode as a string (not to be used for user-facing messages). *)

  val print : t -> Pp.t
  (** Print internal representation (not to be used for user-facing messages). *)

  val debug_to_string : t -> string
  (** Same as [to_string], but outputs extra information related to debug. *)

  val debug_print : t -> Pp.t
  (** Same as [print], but outputs extra information related to debug. *)

end

module Mindset : CSig.USetS with type elt = MutInd.t
[@@ocaml.deprecated "(9.2) This will switch to user ordering at some point in \
the future. In the meantime either use the _env variant or the Q-variant from \
Environ, depending on the desired semantics."]
module Mindmap : Map.UExtS with type key = MutInd.t and module Set := Mindset [@ocaml.warning "-3"]
[@@ocaml.deprecated "(9.2) This will switch to user ordering at some point in \
the future. In the meantime either use the _env variant or the Q-variant from \
Environ, depending on the desired semantics."]

module Mindmap_env : CMap.UExtS with type key = MutInd.t

module Ind :
sig
  (** Designation of a (particular) inductive type. *)
  type t = MutInd.t      (* the name of the inductive type *)
         * int           (* the position of this inductive type
                                    within the block of mutually-recursive inductive types.
                                    BEWARE: indexing starts from 0. *)
  val modpath : t -> ModPath.t

  include QNameS with type t := t

end

type inductive = Ind.t

module Construct :
sig
  (** Designation of a (particular) constructor of a (particular) inductive type. *)
  type t = Ind.t   (* designates the inductive type *)
         * int     (* the index of the constructor
                                    BEWARE: indexing starts from 1. *)

  val modpath : t -> ModPath.t

  include QNameS with type t := t

end

type constructor = Construct.t

module Indset : CSet.ExtS with type elt = inductive
[@@ocaml.deprecated "(9.2) This will switch to user ordering at some point in \
the future. In the meantime either use the _env variant or the Q-variant from \
Environ, depending on the desired semantics."]
module Constrset : CSet.ExtS with type elt = constructor
[@@ocaml.deprecated "(9.2) This will switch to user ordering at some point in \
the future. In the meantime either use the _env variant or the Q-variant from \
Environ, depending on the desired semantics."]

module Indset_env : CSet.ExtS with type elt = inductive
module Constrset_env : CSet.ExtS with type elt = constructor

module Indmap : CMap.ExtS with type key = inductive and module Set := Indset [@ocaml.warning "-3"]
[@@ocaml.deprecated "(9.2) This will switch to user ordering at some point in \
the future. In the meantime either use the _env variant or the Q-variant from \
Environ, depending on the desired semantics."]
module Constrmap : CMap.ExtS with type key = constructor and module Set := Constrset [@ocaml.warning "-3"]
[@@ocaml.deprecated "(9.2) This will switch to user ordering at some point in \
the future. In the meantime either use the _env variant or the Q-variant from \
Environ, depending on the desired semantics."]

module Indmap_env : CMap.ExtS with type key = inductive and module Set := Indset_env
module Constrmap_env : CMap.ExtS with type key = constructor and module Set := Constrset_env

val ith_mutual_inductive : inductive -> int -> inductive
val ith_constructor_of_inductive : inductive -> int -> constructor
val inductive_of_constructor : constructor -> inductive
val index_of_constructor : constructor -> int

(** {6 Hash-consing } *)

val hcons_con : Constant.t Hashcons.f
val hcons_mind : MutInd.t Hashcons.f
val hcons_ind : inductive Hashcons.f
val hcons_construct : constructor Hashcons.f

(******)

type 'a tableKey =
  | ConstKey of 'a
  | VarKey of Id.t
  | RelKey of Int.t

type inv_rel_key = int (** index in the [rel_context] part of environment
                          starting by the end, {e inverse}
                          of de Bruijn indice *)

val eq_table_key : ('a -> 'a -> bool) -> 'a tableKey -> 'a tableKey -> bool
val hash_table_key : ('a -> int) -> 'a tableKey -> int
val eq_constant_key : Constant.t -> Constant.t -> bool

(** {5 Module paths} *)

type module_path = ModPath.t =
  | MPfile of DirPath.t
  | MPbound of MBId.t
  | MPdot of ModPath.t * Id.t
[@@ocaml.deprecated "(8.8) Alias type"]

module Projection : sig
  module Repr : sig
    type t

    val make : inductive -> proj_npars:int -> proj_arg:int -> Id.t -> t

    include QNameS with type t := t

    val constant : t -> Constant.t
    (** Don't use this if you don't have to. *)

    val inductive : t -> inductive
    val mind : t -> MutInd.t
    val npars : t -> int
    val arg : t -> int
    val label : t -> Id.t

    val map : (MutInd.t -> MutInd.t) -> t -> t
    val map_npars : (int -> int) -> t -> t

    val to_string : t -> string
    (** Encode as a string (not to be used for user-facing messages). *)

    val print : t -> Pp.t
    (** Print internal representation (not to be used for user-facing messages). *)

  end
  type t (* = Repr.t * bool *)

  val make : Repr.t -> bool -> t
  val repr : t -> Repr.t

  include QNameS with type t := t

  val constant : t -> Constant.t
  val mind : t -> MutInd.t
  val inductive : t -> inductive
  val npars : t -> int
  val arg : t -> int
  val label : t -> Id.t
  val unfolded : t -> bool
  val unfold : t -> t

  val hcons : t Hashcons.f
  (** Hashconsing of projections. *)

  val map : (MutInd.t -> MutInd.t) -> t -> t
  val map_npars : (int -> int) -> t -> t

  val to_string : t -> string
  (** Encode as a string (not to be used for user-facing messages). *)

  val print : t -> Pp.t
  (** Print internal representation (not to be used for user-facing messages). *)

  val debug_to_string : t -> string
  (** Same as [to_string], but outputs extra information related to debug. *)

  val debug_print : t -> Pp.t
  (** Same as [print], but outputs extra information related to debug. *)

end

module PRset : CSig.USetS with type elt = Projection.Repr.t
module PRmap : Map.UExtS with type key = Projection.Repr.t and module Set := PRset

(** Predicate on projection representation (ignoring unfolding state) *)
module PRpred : Predicate.S with type elt = Projection.Repr.t

(** {6 Global reference is a kernel side type for all references together } *)

module GlobRef : sig

  type t =
    | VarRef of variable           (** A reference to the section-context. *)
    | ConstRef of Constant.t       (** A reference to the environment. *)
    | IndRef of inductive          (** A reference to an inductive type. *)
    | ConstructRef of constructor  (** A reference to a constructor of an inductive type. *)

  val is_bound : t -> bool

  include QNameS with type t := t

  module Set_env : CSig.USetS with type elt = t
  module Map_env : Map.UExtS
    with type key = t and module Set := Set_env

  module Set : CSig.USetS with type elt = t
  [@@ocaml.deprecated "(9.2) This will switch to user ordering at some point in \
  the future. In the meantime either use the _env variant or the Q-variant from \
  Environ, depending on the desired semantics."]

  module Map : Map.UExtS
    with type key = t and module Set := Set [@@ocaml.warning "-3"]

  val print : t -> Pp.t
  (** Print internal representation (not to be used for user-facing messages). *)

end

(** Located identifiers and objects with syntax. *)

type lident = Id.t CAst.t
type lname = Name.t CAst.t
type lstring = string CAst.t

val lident_eq : lident -> lident -> bool

(** Deprecated *)
module Label : sig
  type t = Id.t
  (** Type of labels *)

  val equal : t -> t -> bool
  (** Equality over labels *)

  val compare : t -> t -> int
  (** Comparison over labels. *)

  val hash : t -> int
  (** Hash over labels. *)

  val make : string -> t
  (** Create a label out of a string. *)

  val of_id : Id.t -> t
  (** Conversion from an identifier. *)

  val to_id : t -> Id.t
  (** Conversion to an identifier. *)

  val to_string : t -> string
  (** Conversion to string. *)

  val print : t -> Pp.t
  (** Pretty-printer. *)

  module Set : Set.ExtS with type elt = t
  module Map : Map.ExtS with type key = t and module Set := Set

  val hcons : t Hashcons.f

end [@@deprecated "(9.2) Use Id"]
