(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module type Staged = sig

  (** Blob containing the global state at this stage. *)
  type t

  (** Mutable wrapper around the global state (essentially [t ref],
      but in Interp stage [t] contains the synterp state and [mut]
      does not allow modifying the synterp state). *)
  type mut

  val get : mut -> t
  val set : mut -> t -> unit
  val with_mut : (mut -> 'a) -> t -> t * 'a

  type 'a v = {
    get : t -> 'a;
    set : mut -> 'a -> unit;
  }

  (** We provide safe projection from the summary to the types stored in it.*)
  type _ tag

  (** Types of global Rocq states. The ['v] type should be pure but
      doesn't need to be marshallable, and can be efficiently
      accessed. The ['frozen] type should be pure and marshallable by
      the standard OCaml marshalling functions.

      NB: ['v = unit] means the accessible state is handled outside [t]. *)
  type ('v,'frozen) declaration = {
    freeze : 'v -> 'frozen;
    unfreeze : 'frozen -> 'v;
    init : unit -> 'v;
  }

  val declare : string -> ('v,'frozen) declaration -> 'v v
  val declare_tag : string -> ('v,'frozen) declaration -> 'v v * 'frozen tag

  (** Common case where ['v] is marshallable, [freeze] and [unfreeze] are the identity. *)
  val simple_declaration : 'v -> ('v,'v) declaration

  val declare_simple : string -> 'v -> 'v v

  (** Legacy API, TODO deprecate *)
  val ref : name:string -> 'v -> 'v ref
  val ref_tag : name:string -> 'v -> 'v ref * 'v tag
  val local_ref : name:string -> 'v -> (unit -> 'v) * ('v -> unit)

  (** Declare a state which will not be sent to other processes (e.g. proof workers).
      ['v] does not need to be marshallable. *)
  val declare_local : string -> 'v -> 'v v

  (** The type [frozen] is a snapshot of the states of all the registered
      tables of the system. *)
  type frozen

  val empty_frozen : frozen
  val freeze_summaries : t -> frozen

  (** Unfreeze doesn't use the data in the [mut] argument, but it may
      modify imperative global state so we require a [mut] handle
      instead of having type [frozen -> t]. *)
  val unfreeze_summaries : ?partial:bool -> frozen -> mut -> unit

  val init_summaries : unit -> t

  (** Act on the frozen summary. Experimental API, use with CARE *)
  val project_from_summary : frozen -> 'a tag -> 'a
  val modify_summary : frozen -> 'a tag -> 'a -> frozen
  val remove_from_summary : frozen -> 'a tag -> frozen

  (** Intercept newly declared summaries (from loading plugins) *)
  type any_summary
  val capture_new_summaries : (unit -> 'a) -> any_summary list * 'a
  val init_new_summaries : any_summary list -> mut -> unit

  val init_missing_summaries : mut -> unit

  (** Debug  *)
  val dump : unit -> (int * string) list
end
