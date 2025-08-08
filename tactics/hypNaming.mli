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
open EConstr
open Environ
open Evd
open Logic

(** Utility functions to help with naming hypotheses (e.g. for [intro]). *)

(** {6 Automatic clearing of hypotheses. } *)

(** [use_clear_hyp_by_default ()] returns the default clear flag used by [apply] and related tactics.
    - [true] means that hypotheses are cleared after being applied.
    - [false] means that hypotheses are kept after being applied. *)
val use_clear_hyp_by_default : unit -> bool

(** [apply_clear_request c1 c2 id] implements the clear behaviour of [apply] and friends.
    - [c1] is the primary clear flag. If [None] we use the secondary clear flag.
    - [c2] is the secondary clear flag, usually [use_clear_hyp_by_default ()].
    - [id] is the identifier of the hypothesis to clear. If [None] we do nothing. *)
val apply_clear_request : bool option -> bool -> Id.t option -> unit Proofview.tactic

(** {6 Fresh name generation. } *)

(** [fresh_id_in_env avoid id env] generates a fresh identifier built from [id].
    The returned identifier is guaranteed to be distinct from:
    - The identifiers in [avoid].
    - The global constants in [env].
    - The local variables in [env]. *)
val fresh_id_in_env : Id.Set.t -> Id.t -> env -> Id.t

(** [default_id env sigma decl] computes a default identifier used to introduce
    a declaration [decl]. *)
val default_id : env -> evar_map -> (constr, constr, 'a) Context.Rel.Declaration.pt -> Id.t

(** {6 Naming introduced hypotheses. } *)

(** A [name_flag] specifies how to choose a name when introducing a hypothesis.
    - [NamingAvoid ids] generates a fresh name, avoiding [ids] and any already used name.
    - [NamingBasedOn (id, ids)] generates a fresh name based on [id],
      avoiding [ids] and any already used name.
    - [NamingMustBe id] picks name [id]. *)
type name_flag =
  | NamingAvoid of Id.Set.t
  | NamingBasedOn of Id.t * Id.Set.t
  | NamingMustBe of lident

(** [naming_of_name name] returns the canonical name flag for [name].
    - If [name] is [Anonymous] then a fresh name will be generated.
    - If [name] is [Name id] then [x] will get picked. *)
val naming_of_name : Name.t -> name_flag

(** [naming_of_id_opt idopt avoid] builds a name flag for [idopt].
    - if [idopt] is [Some id] then [NamingMustBe id] is returned.
    - if [idopt] is [None] then [NamingAvoid avoid] is returned. *)
val naming_of_id_opt : Id.t option -> Id.Set.t -> name_flag

(** [find_name ~replace decl naming goal] generates a fresh name in the goal [goal]
    for the name flag [naming].
    - [replace]: if [true] then [NamingMustBe] will replace any previous hypothesis.
      If [false] then attempting to replace a hypothesis will throw an exception.
      Defaults to [false].
    - [decl]: used to generate the base name for [NamingAvoid]. *)
val find_name : ?replace:bool -> (constr, constr, 'a) Context.Rel.Declaration.pt ->
  name_flag -> Proofview.Goal.t -> Id.t

(** [find_intro_names env sigma ctx] returns the names that would be created by [intros],
    without actually doing [intros].  *)
val find_intro_names : env -> Evd.evar_map -> rel_context -> Id.t list

(** {6 Computing position of hypotheses for replacing. } *)

val get_next_hyp_position : env -> evar_map -> Id.t -> named_context -> Id.t move_location

val get_previous_hyp_position : env -> evar_map -> Id.t -> named_context -> Id.t move_location
