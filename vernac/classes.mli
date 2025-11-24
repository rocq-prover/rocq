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
open Environ
open Constrexpr
open Typeclasses

(** Instance declaration *)

val declare_instance : Summary.Interp.mut ->
  ?warn:bool -> env -> Evd.evar_map ->
  hint_info option -> Hints.hint_locality -> GlobRef.t -> unit
(** Declares the given global reference as an instance of its type.
    Does nothing — or emit a “not-a-class” warning if the [warn] argument is set —
    when said type is not a registered type class. *)

val existing_instance : Summary.Interp.mut ->
  ?loc:Loc.t -> Hints.hint_locality -> GlobRef.t -> Vernacexpr.hint_info_expr option -> unit
(** globality, reference, optional priority and pattern information *)

val new_instance_interactive
  : locality:Hints.hint_locality
  -> poly:bool
  -> name_decl
  -> local_binder_expr list
  -> constr_expr
  -> ?tac:unit Proofview.tactic
  -> ?hook:(Summary.Interp.mut -> GlobRef.t -> unit)
  -> Vernacexpr.hint_info_expr
  -> (bool * constr_expr) option
  -> lident * Declare.Proof.t

val new_instance
  : Summary.Interp.mut
  -> locality:Hints.hint_locality
  -> poly:bool
  -> name_decl
  -> local_binder_expr list
  -> constr_expr
  -> (bool * constr_expr)
  -> ?hook:(Summary.Interp.mut -> GlobRef.t -> unit)
  -> Vernacexpr.hint_info_expr
  -> lident

val new_instance_program
  : Summary.Interp.mut
  -> locality:Hints.hint_locality
  -> pm:Declare.OblState.t
  -> poly:bool
  -> name_decl
  -> local_binder_expr list
  -> constr_expr
  -> (bool * constr_expr) option
  -> ?hook:(Summary.Interp.mut -> GlobRef.t -> unit)
  -> Vernacexpr.hint_info_expr
  -> Declare.OblState.t * lident

val declare_new_instance
  : Summary.Interp.mut
  -> locality:Hints.hint_locality
  -> program_mode:bool
  -> poly:bool
  -> ident_decl
  -> local_binder_expr list
  -> constr_expr
  -> Vernacexpr.hint_info_expr
  -> unit

val add_class : Summary.Interp.mut -> typeclass -> unit

type instance = {
  class_name : GlobRef.t;
  instance : GlobRef.t;
  info : Typeclasses.hint_info;
  locality : Hints.hint_locality;
}

module Event : sig
  type t =
    | NewClass of typeclass
    | NewInstance of instance
end

(** Activated observers are called whenever a class or an instance are declared.

    [register_observer] is to be called once per process for a given
    string, unless [override] is [true]. The registered observer is not activated.

    Activation state is part of the summary. It is up to the caller to
    use libobject for persistence if desired.
*)

type observer

val register_observer : name:string -> ?override:bool -> (Event.t -> unit) -> observer

val activate_observer : observer -> unit

val deactivate_observer : observer -> unit

(** Setting opacity *)

val set_typeclass_transparency
  : Summary.Interp.mut
  -> ?typeclasses_db:Hints.hint_db_name
  -> locality:Hints.hint_locality
  -> Evaluable.t list
  -> bool
  -> unit

val set_typeclass_transparency_com
  : Summary.Interp.mut
  -> locality:Hints.hint_locality
  -> Libnames.qualid list
  -> bool
  -> unit

val set_typeclass_mode
  : Summary.Interp.mut
  -> ?typeclasses_db:string
  -> locality:Hints.hint_locality
  -> GlobRef.t
  -> Hints.hint_mode list
  -> unit

(** For generation on names based on classes only *)

val refine_att : bool Attributes.attribute

(** {6 Low level interface used by Add Morphism, do not use } *)
module Internal :
sig
  val add_instance : Summary.Interp.mut ->
    typeclass -> hint_info -> Hints.hint_locality -> GlobRef.t -> unit
end


(** A configurable warning to output if a default mode is used for a class declaration. *)
val warn_default_mode : ?loc:Loc.t -> (GlobRef.t * Hints.hint_mode list) -> unit
