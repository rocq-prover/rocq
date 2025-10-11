(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This module registers the declaration of global tables, which will be kept
    in synchronization during the various backtracks of the system. *)

module Stage : sig

(** We distinguish two stages and separate the system state accordingly.
    [Synterp] is the syntactic interpretation phase, i.e. vernacular parsing and
    execution of commands having an effect on parsing. [Interp] is the
    interpretation phase, where standard commands are executed. *)
  type t = Synterp | Interp

  val equal : t -> t -> bool

end

(** Token to access the summary state.
    It is mutable even with "read", "read" only disallows mutating with that token
    (equivalent of the (fun () -> !x) closure for a ref).

    The actual state is still globally imperative (for now?).
*)
type (-'synterp_rw, -'interp_rw) t
(* we can also use covariant, readwrite = RW, read = RW|R, nothing = RW|R|Nothing
   but the errors are worse IMO

   or we make it invariant and use explicit cast functions? could get heavy
*)

(** In synterp stage, the interp state is not accessible. *)
type nothing = [`Nothing]

(** In interp stage, the synterp state is read-only. *)
type read = [`R|`Nothing]

(** The state matching the current stage is read-write. *)
type readwrite = [`RW|`R|`Nothing]

(** Types of global Rocq states. The ['a] type should be pure and marshallable by
    the standard OCaml marshalling function. *)
type 'a summary_declaration = {
  stage : Stage.t;
  freeze_function : unit -> 'a;
  unfreeze_function : 'a -> unit;
  init_function : unit -> unit;
}

(** For tables registered during the launch of rocq repl, the [init_function]
    will be run only once, during an [init_summaries] done at the end of
    coqtop initialization. For tables registered later (for instance
    during a plugin dynlink), [init_function] is used when unfreezing
    an earlier frozen state that doesn't contain any value for this table.

    Beware: for tables registered dynamically after the initialization
    of Coq, their init functions may not be run immediately. It is hence
    the responsibility of plugins to initialize themselves properly.
*)

(** Registers some global imperative state with the summary. Accessing
    the state (except for the functions in [summary_declaration]
    should be protected by requiring an appropriately typed token. *)
val declare_summary : string -> ?make_marshallable:('a -> 'a) -> 'a summary_declaration -> unit

(** We provide safe projection from the summary to the types stored in
   it.*)
module Dyn : Dyn.S

val declare_summary_tag : string -> ?make_marshallable:('a -> 'a) -> 'a summary_declaration -> 'a Dyn.tag

(** All-in-one reference declaration + summary registration + access control.

    When [local:true] the value is local to the process, i.e. not sent to proof workers.
    Consequently it doesn't need to be of a marshallable type.
    It is useful to implement a local cache for example.

    [ref_tag] is never local.

    If you bind the result as eg [let { read = (!); write = (:=) } =
    ref ...] it behaves as projecting a regular [Stdlib.ref] from the
    summary state.
*)

(* XXX is there some GADT trick to avoid needing separate APIs for synterp/interp?
   Or should we do separate modules as is done in Lib? *)
type 'v declared_synterp = {
  sread : 'syn 'interp. ([>read] as 'syn, 'interp) t -> 'v;
  swrite : 'interp. (readwrite, 'interp) t -> 'v -> unit;
}

type 'v declared_interp = {
  read : 'syn 'interp. ('syn, [>read] as 'interp) t -> 'v;
  write : 'syn. ('syn, readwrite) t -> 'v -> unit;
}

val ref : ?local:bool -> name:string -> 'a -> 'a declared_interp
val syn_ref : name:string -> 'a -> 'a declared_synterp
val ref_tag : name:string -> 'a -> 'a declared_interp * 'a Dyn.tag

(** Special summary for ML modules.  This summary entry is special
    because its unfreeze may load ML code and hence add summary
    entries.  Thus is has to be recognizable, and handled properly.

    The args correspond to Mltop.PluginSpec.t, that is to say, the
    findlib name for the plugin.  *)
val declare_ml_modules_summary : string list summary_declaration -> unit

(** For global tables registered statically before the end of coqtop
    launch, the following empty [init_function] could be used. *)

val nop : unit -> unit

module type FrozenStage = sig

  (** Access token. *)
  type -'rw t

  type nonrec 'a read = ([>read] as 'a) t
  type nonrec readwrite = readwrite t

  (** The type [frozen] is a snapshot of the states of all the registered
      tables of the system. *)
  type frozen

  (** These globally available tokens should go away eventually. *)
  (* XXX freeze, init should take a token and unfreeze return a token? *)
  val read : [`Nothing|`R] read
  val readwrite : readwrite

  val empty_frozen : frozen
  val freeze_summaries : unit -> frozen
  val make_marshallable : frozen -> frozen
  val unfreeze_summaries : ?partial:bool -> frozen -> unit
  val init_summaries : unit -> unit
  val project_from_summary : frozen -> 'a Dyn.tag -> 'a

end

module Synterp : FrozenStage with type 'rw t = ('rw, nothing) t
module Interp : sig

  include FrozenStage with type 'rw t = (read, 'rw) t

  (** Typed projection of the summary. Experimental API, use with CARE *)

  val modify_summary : frozen -> 'a Dyn.tag -> 'a -> frozen
  val remove_from_summary : frozen -> 'a Dyn.tag -> frozen

end

(** {6 Debug} *)
val dump : unit -> (int * string) list
(* XXX token *)
