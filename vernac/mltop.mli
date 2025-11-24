(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** {5 Toplevel management} *)

(** Coq plugins are identified by their OCaml library name (in the
   Findlib sense) *)
module PluginSpec : sig

  (** A plugin is identified by its canonical library name,
      such as [rocq-runtime.plugins.ltac] *)
  type t

  (** [to_package p] returns the findlib name of the package *)
  val to_package : t -> string

  val pp : t -> string
end

type toplevel =
  { load_plugin : PluginSpec.t -> unit
  (** Load a findlib library, given by public name *)
  ; load_module : string -> unit
  (** Load a cmxs / cmo module, used by the native compiler to load objects *)
  ; add_dir  : string -> unit
  (** Adds a dir to the module search path *)
  ; ml_loop  : ?init_file:string -> unit -> unit
  (** Run the OCaml toplevel with given addtitional initialisation file *)
  }

(** Sets and initializes a toplevel (if any) *)
val set_top : toplevel -> unit

(** Low level module loading, for the native compiler and similar users. *)
val load_module : string -> unit

(** Removes the toplevel (if any) *)
val remove : unit -> unit

(** Tests if an Ocaml toplevel runs under Coq *)
val is_ocaml_top : unit -> bool

(** Starts the Ocaml toplevel loop *)
val ocaml_toploop : ?init_file:string -> unit -> unit

(** {5 ML Dynlink} *)

(** Adds a dir to the plugin search path, this also extends
   OCamlfind's search path *)
val add_ml_dir : string -> unit

(** Tests if we can load ML files *)
val has_dynlink : bool

(** {5 Initialization functions} *)

(** Declare a initialization function. The initialization function is
    called in Declare ML Module, including reruns after backtracking
    over it (either interactive backtrack, module closing backtrack,
    Require of a file with Declare ML Module).
*)
val add_init_function : string -> (unit -> unit) -> unit

(** Register a callback that will be called when the module is declared with
    the Declare ML Module command. This is useful to define Coq objects at that
    time only. Several functions can be defined for one module; they will be
    called in the order of declaration, and after the ML module has been
    properly initialized.

    Unlike the init functions it does not run after closing a module
    or Requiring a file which contains the Declare ML Module.
    This allows to have effects which depend on the module when
    command was run in, eg add a named libobject which will use it for the prefix.

    The callback runs in the synterp phase, use
    [declare_cache_obj_full] if you also need to interact with Interp
    state.
*)
val declare_cache_obj : (Summary.Synterp.mut -> unit) -> string -> unit

type cache_obj = CacheObj : {
    synterp : Summary.Synterp.mut -> 'a;
    interp : Summary.Interp.mut -> 'a -> unit;
  } -> cache_obj

val interp_only_obj : (Summary.Interp.mut -> unit) -> cache_obj

(** Register a callback with an interp phase. *)
val declare_cache_obj_full : cache_obj -> string -> unit

(** {5 Declaring modules} *)

type interp_fun

val run_interp_fun : interp_fun -> Summary.Interp.mut -> unit

(** Implementation of the [Declare ML Module] vernacular command. *)
val declare_ml_modules : Summary.Synterp.mut -> Vernacexpr.locality_flag -> string list -> Summary.Interp.any_summary list * interp_fun

val new_interp : Summary.Interp.mut -> bool -> Summary.Interp.any_summary list -> unit

(** {5 Utilities} *)

val print_ml_modules : unit -> Pp.t
val print_gc : unit -> Pp.t
