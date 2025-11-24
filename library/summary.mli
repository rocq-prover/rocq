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

module Synterp : sig

  include Summary_intf.Staged

  type ml_modules = string list

  (** Special summary for ML modules.  This summary entry is special
      because its unfreeze may load ML code and hence add summary
      entries.  Thus it has to be recognizable, and handled properly.

      The [string]s correspond to Mltop.PluginSpec.t , that is to say, the
      findlib name for the plugin.  *)
  val declare_ml_modules_summary : (unit,ml_modules) declaration -> unit

end

module Interp : sig

  (** Type containing only the interp state. *)
  type interp_only
  type interp_only_mut

  type 'a with_synterp = { synterp : Synterp.t; interp : 'a }

  include Summary_intf.Staged
    with type t = interp_only with_synterp
     and type mut = interp_only_mut with_synterp

  val unfreeze_summaries : ?partial:bool -> frozen -> mut -> unit
  val init_summaries : Synterp.t -> t

end

(** Alias for Synterp/Interp.ref depending on stage, TODO deprecate *)
val ref : ?stage:Stage.t -> name:string -> 'v -> 'v ref

module StageG : sig

  type (_,_) t =
    | SynterpG : (Synterp.t,Synterp.mut) t
    | InterpG : (Interp.t,Interp.mut) t

  val equal : ('a1,'b1) t -> ('a2,'b2) t -> ('a1 * 'b1, 'a2 * 'b2) Util.eq option

end

val empty : Interp.t
val init : unit -> Interp.t

(** Execute something mutating both phases. *)
val run_synterp_interp : (Synterp.mut -> 'a) -> (Interp.mut -> 'a -> 'b) -> Interp.t ref -> 'b

val run_interp : (Interp.mut -> 'a) -> Interp.t ref -> 'a
