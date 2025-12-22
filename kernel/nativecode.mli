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
open Constr
open Declarations
open Environ
open Nativevalues

(** This file defines the mllambda code generation phase of the native
compiler. mllambda represents a fragment of ML, and can easily be printed
to OCaml code. *)

type cenv

val make_cenv : unit -> cenv
val get_cenv_symbols : cenv -> symbols

type global

val debug_native_compiler : CDebug.t

val keep_debug_files : unit -> bool

val pp_global : Format.formatter -> global -> unit

val mk_open : string -> global

val get_value : symbols -> int -> Nativevalues.t

val get_sort : symbols -> int -> Sorts.t

val get_name : symbols -> int -> Name.t

val get_const : symbols -> int -> Constant.t

val get_match : symbols -> int -> Nativevalues.annot_sw

val get_ind : symbols -> int -> inductive

val get_evar : symbols -> int -> Evar.t

val get_instance : symbols -> int -> UVars.Instance.t

val get_proj : symbols -> int -> inductive * int

type code_location_updates
type linkable_code = global list * symbols * code_location_updates

val empty_updates : code_location_updates

val register_native_file : string -> unit

val is_loaded_native_file : string -> bool

val compile_constant_field : cenv -> env -> Constant.t ->
  global list -> constant_body -> global list

val compile_mind_field : cenv -> ModPath.t -> Id.t ->
  global list -> mutual_inductive_body -> global list

val compile_rewrite_rules : env -> Id.t ->
  global list -> rewrite_rules_body -> global list

val mk_conv_code : env -> Genlambda.evars -> string -> constr -> constr -> linkable_code
val mk_norm_code : env -> Genlambda.evars -> string -> constr -> linkable_code

val mk_library_header : Nativevalues.symbols -> global list

val mod_uid_of_dirpath : DirPath.t -> string

val link_info_of_dirpath : DirPath.t -> link_info

val update_locations : code_location_updates -> unit

val add_header_comment : global list -> string -> global list
