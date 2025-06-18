(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This file provides facilities to access OCaml compiler and dynamic linker,
used by the native compiler. *)

(** For build compatibility *)
module CRef : sig
  type 'a ref = 'a CRef.ref
  val ref : 'a -> 'a ref
  val (!) : 'a ref -> 'a
  val (:=) : 'a ref -> 'a -> unit
  val incr : int ref -> unit
end

(* Directory where compiled files are stored *)
val output_dir : CUnix.physical_path CRef.ref
val include_dirs : CUnix.physical_path list CRef.ref

(** Default value for include dirs in non -boot mode (just the kernel). *)
val default_include_dirs : Boot.Env.t -> CUnix.physical_path list

val get_load_paths : (unit -> string list) CRef.ref

val load_obj : (string -> unit) CRef.ref

val get_ml_filename : unit -> string * string

(** [compile file code ~profile] will compile native [code] to [file],
   and return the name of the object file; this name depends on
   whether are in byte mode or not; file is expected to be .ml file *)
val compile : string -> Nativecode.global list -> profile:bool -> string

type native_library = Nativecode.global list * Nativevalues.symbols

(** [compile_library (code, _) file] is similar to [compile file code]
   but will perform some extra tweaks to handle [code] as a Rocq lib. *)
val compile_library : native_library -> string -> unit

(** [execute_library file upds] dynamically loads library [file],
    updates the library locations [upds], and returns the values stored
    in [rt1] and [rt2] *)
val execute_library :
  prefix:string -> string -> Nativecode.code_location_updates ->
  Nativevalues.t option * Nativevalues.t option

(** [enable_library] marks the given library for dynamic loading
    the next time [link_libraries] is called. *)
val enable_library : string -> Names.DirPath.t -> unit

val link_libraries : unit -> unit

(* used for communication with the loaded libraries *)
(* EJGA: XXX Fixme, this should be in TLS, however some weird problems do happen with dynlink *)
val rt1 : Nativevalues.t option CRef.ref
val rt2 : Nativevalues.t option CRef.ref
