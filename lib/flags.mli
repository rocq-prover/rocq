(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Global options of the system. *)

(** WARNING: don't add new entries to this file!

    This file is own its way to deprecation in favor of a purely
   functional state, but meanwhile it will contain options that are
   truly global to the system such as [debug]

    If you are thinking about adding a global flag, well, just
   don't. First of all, options make testins exponentially more
   expensive, due to the growth of flag combinations. So please make
   some effort in order for your idea to work in a configuration-free
   manner.

    If you absolutely must pass an option to your new system, then do
   so as a functional argument so flags are exposed to unit
   testing. Then, register such parameters with the proper
   state-handling mechanism of the top-level subsystem of Rocq.

 *)

(** Command-line flags  *)

(** Async-related flags *)
val async_proofs_worker_id : string ref
val async_proofs_is_worker : unit -> bool

(** Debug flags *)
val in_debugger : bool ref
val in_ml_toplevel : bool ref

(* Used to check stages are used correctly. *)
val in_synterp_phase : bool option ref

(* Rocq quiet mode. Note that normal mode is called "verbose" here,
   whereas [quiet] suppresses normal output such as goals in rocq repl *)
val quiet : bool ref
val silently : ('a -> 'b) -> 'a -> 'b
val verbosely : ('a -> 'b) -> 'a -> 'b
val if_silent : ('a -> unit) -> 'a -> unit
val if_verbose : ('a -> unit) -> 'a -> unit

(** [with_modified_ref r nf f x] Temporarily modify a reference in the
    call to [f x] . Be very careful with these functions, it is very
    easy to fall in the typical problem with effects:

    with_modified_ref r nf f x y != with_modified_ref r nf (f x) y

*)
val with_modified_ref : 'c ref -> ('c -> 'c) -> ('a -> 'b) -> 'a -> 'b

(** Temporarily activate an option (to activate option [o] on [f x y z],
   use [with_option o (f x y) z]) *)
val with_option : bool ref -> ('a -> 'b) -> 'a -> 'b

(** As [with_option], but on several flags. *)
val with_options : bool ref list -> ('a -> 'b) -> 'a -> 'b

(** Temporarily deactivate an option *)
val without_option : bool ref -> ('a -> 'b) -> 'a -> 'b

(** Flag set when the test-suite is called.
    - display verbose information for [Fail]
    - print quickfix info in error printers *)
val test_mode : bool ref
