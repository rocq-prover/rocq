(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** {6 [Mod_subst] } *)

open Names
open Constr

(** {6 Delta resolver} *)

(** A delta resolver is a renaming of kernames and modpaths.
    Objects on which the resolver acts non-trivially must share a common modpath
    prefix called the root of the resolver. *)
type delta_resolver

(** Given a root, build a resolver. *)
val empty_delta_resolver : ModPath.t -> delta_resolver

val has_root_delta_resolver : ModPath.t -> delta_resolver -> bool

(** [add_mp_delta_resolver mp v reso] assumes that root(reso) ⊆ mp. *)
val add_mp_delta_resolver :
  ModPath.t -> ModPath.t -> delta_resolver -> delta_resolver

(** [add_kn_delta_resolver kn v reso] assumes that root(reso) ⊆ modpath(kn). *)
val add_kn_delta_resolver :
  KerName.t -> KerName.t -> delta_resolver -> delta_resolver

(** [add_inline_delta_resolver kn v reso] assumes that root(reso) ⊆ modpath(kn). *)
val add_inline_delta_resolver :
  KerName.t -> (int * constr UVars.univ_abstracted option) -> delta_resolver -> delta_resolver

(** [add_delta_resolver reso1 reso2] merges two renamings, assuming that
    root(reso2) ⊆ root(reso1). Note that this is asymmetrical. The root of the
    result is root(reso2). *)
val add_delta_resolver : delta_resolver -> delta_resolver -> delta_resolver

(** Assuming mp ⊆ root(delta), [upcast_delta_resolver mp delta] allows seeing
    [delta] as a resolver with root = mp. *)
val upcast_delta_resolver : ModPath.t -> delta_resolver -> delta_resolver

(** Effect of a [delta_resolver] on a module path, on a kernel name *)

val mp_of_delta : delta_resolver -> ModPath.t -> ModPath.t
val kn_of_delta : delta_resolver -> KerName.t -> KerName.t

(** Build a constant whose canonical part is obtained via a resolver *)

val constant_of_delta_kn : delta_resolver -> KerName.t -> Constant.t

(** Same for inductive names *)

val mind_of_delta_kn : delta_resolver -> KerName.t -> MutInd.t

(** Extract the set of inlined constant in the resolver *)
val inline_of_delta : int option -> delta_resolver -> (int * KerName.t) list

(** Does a [delta_resolver] contains a [mp]? *)

val mp_in_delta : ModPath.t -> delta_resolver -> bool

(** {6 Substitution} *)

type substitution

val empty_subst : substitution

val is_empty_subst : substitution -> bool

(** add_* add [arg2/arg1]\{arg3\} to the substitution with no sequential
   composition. Most often this is not what you want. For sequential
   composition, try [join (map_mbid mp delta) subs] **)
val add_mbid :
  MBId.t -> ModPath.t -> delta_resolver  -> substitution -> substitution
val add_mp :
  ModPath.t -> ModPath.t -> delta_resolver -> substitution -> substitution

(** map_* create a new substitution [arg2/arg1]\{arg3\} *)
val map_mbid :
  MBId.t -> ModPath.t -> delta_resolver -> substitution
val map_mp :
  ModPath.t -> ModPath.t -> delta_resolver -> substitution

(** sequential composition:
   [substitute (join sub1 sub2) t = substitute sub2 (substitute sub1 t)]
*)
val join : substitution -> substitution -> substitution


(** Apply the substitution on the domain of the resolver  *)
val subst_dom_delta_resolver : substitution -> delta_resolver -> delta_resolver

(** Apply the substitution on the codomain of the resolver  *)
val subst_codom_delta_resolver :
  substitution -> delta_resolver -> delta_resolver

val subst_dom_codom_delta_resolver :
  substitution -> delta_resolver -> delta_resolver


(**/**)
(* debugging *)
val debug_string_of_subst : substitution -> string
val debug_pr_subst : substitution -> Pp.t
val debug_string_of_delta : delta_resolver -> string
val debug_pr_delta : delta_resolver -> Pp.t
(**/**)

(** [subst_mp sub mp] guarantees that whenever the result of the
   substitution is structutally equal [mp], it is equal by pointers
   as well [==] *)

val subst_mp :
  substitution -> ModPath.t -> ModPath.t

val subst_mind :
  substitution -> MutInd.t -> MutInd.t

val subst_ind :
  substitution -> inductive -> inductive

val subst_constructor :
  substitution -> constructor -> constructor

val subst_pind : substitution -> pinductive -> pinductive

val subst_kn :
  substitution -> KerName.t -> KerName.t

val subst_con :
  substitution -> Constant.t -> Constant.t * constr UVars.univ_abstracted option

val subst_pcon :
  substitution -> pconstant -> pconstant

val subst_constant :
  substitution -> Constant.t -> Constant.t

val subst_proj_repr : substitution -> Projection.Repr.t -> Projection.Repr.t
val subst_proj : substitution -> Projection.t -> Projection.t

val subst_retro_action : substitution -> Retroknowledge.action -> Retroknowledge.action

(** [replace_mp_in_con mp mp' con] replaces [mp] with [mp'] in [con] *)
val replace_mp_in_kn : ModPath.t -> ModPath.t -> KerName.t -> KerName.t

(** [subst_mps sub c] performs the substitution [sub] on all kernel
   names appearing in [c] *)
val subst_mps : substitution -> constr -> constr
val subst_mps_list : substitution list -> constr -> constr

val is_rerooted_delta : delta_resolver -> delta_resolver -> bool
