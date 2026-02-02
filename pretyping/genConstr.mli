(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Tags for extensible terms. The [raw] type is contained in
    constrexpr, and the [glb] type in glob terms. *)
type ('raw, 'glb) tag

(** Create a new tag. Tags should be registered with
    [GlobEnv.register_constr_interp0], [Genintern.register_intern_constr],
    [Gensubst.register_constr_subst] and [Genprint.register_constr_print].

    Also optionally
    - [Genintern.register_ntn_subst0] (to be used in notations)

    - [Genintern.register_intern_pat] and [Genintern.register_interp_pat]
      (to be used in tactic patterns)
*)
val create : string -> _ tag

val eq : ('raw1, 'glb1) tag -> ('raw2, 'glb2) tag -> ('raw1 * 'glb1, 'raw2 * 'glb2) Util.eq option

val repr : _ tag -> string

type raw = Raw : ('raw, _) tag * 'raw -> raw

type glb = Glb : (_, 'glb) tag * 'glb -> glb

module Register (M : sig type ('raw, 'glb) t end) : sig
  val register : ('raw, 'glb) tag -> ('raw, 'glb) M.t -> unit

  val mem : _ tag -> bool

  val find_opt : ('raw, 'glb) tag -> ('raw, 'glb) M.t option

  (** Assert false if not present *)
  val get : ('raw, 'glb) tag -> ('raw, 'glb) M.t
end
