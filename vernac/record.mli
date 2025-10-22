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
open Vernacexpr
open Constrexpr
open Structures

module Data : sig
  type coercion_flags = {
    coe_local : bool;
    coe_reversible : bool;
  }
  type instance_flags = {
    inst_locality : Hints.hint_locality;
    inst_priority : int option;
  }
  type projection_flags = {
    pf_coercion: coercion_flags option;
    pf_instance: instance_flags option;
    pf_canonical: bool;
  }
  type t = {
    is_coercion : Vernacexpr.coercion_flag;
    proj_flags : projection_flags list;
  }
end

module Ast : sig
  type t =
    { name : Names.lident
    ; is_coercion : coercion_flag
    ; binders: local_binder_expr list
    ; cfs : (local_decl_expr * Data.projection_flags * notation_declaration list) list
    ; idbuild : lident
    ; sort : constr_expr option
    ; default_inhabitant_id : Id.t option
    }
end

val definition_structure
  : flags:ComInductive.flags
  -> cumul_univ_decl_expr option
  -> inductive_kind
  -> primitive_proj:bool
  -> Ast.t list
  -> GlobRef.t list

module RecordEntry : sig

  type one_ind_info = {
    (* inhabitant_id not redundant with the entry in non prim record case *)
    inhabitant_id : Id.t;
    default_dep_elim : DeclareInd.default_dep_elim;
    (* implfs includes the param and principal argument info *)
    implfs : Impargs.manual_implicits list;
    fieldlocs : Loc.t option list;
  }

  type t = {
    global_univs : PConstraints.ContextSet.t;
    ubinders : UState.named_universes_entry;
    mie : Entries.mutual_inductive_entry;
    ind_infos : one_ind_info list;
    param_impls : Impargs.manual_implicits;
  }

end

(** A record is an inductive [mie] with extra metadata *)
module Record_decl : sig
  type t = {
    entry : RecordEntry.t;
    records : Data.t list;
    projections_kind : Decls.definition_object_kind;
    indlocs : DeclareInd.indlocs;
  }
end

(** Ast.t list at the constr level *)
val interp_structure
  : flags:ComInductive.flags
  -> cumul_univ_decl_expr option
  -> inductive_kind
  -> primitive_proj:bool
  -> Ast.t list
  -> Record_decl.t


val declare_existing_class : GlobRef.t -> unit

val canonical_inhabitant_id : isclass:bool -> Id.t -> Id.t

(* Implementation internals, consult Rocq developers before using;
   current user Elpi, see https://github.com/LPCIC/coq-elpi/pull/151 *)
module Internal : sig
  val declare_projections
    : Names.inductive
    -> kind:Decls.definition_object_kind
    -> inhabitant_id:Names.Id.t
    -> Data.projection_flags list
    -> ?fieldlocs:Loc.t option list
    -> Impargs.manual_implicits list
    -> Structure.projection list

  val declare_structure_entry : Structure.t -> unit

end
