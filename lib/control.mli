(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Global control of Rocq. *)

(** Used to convert signals to exceptions *)
exception Timeout

(** Will periodically call [Thread.delay] if set to true *)
val enable_thread_delay : bool ref

val interrupt : bool ref
(** Rocq interruption: set the following boolean reference to interrupt Rocq
    (it eventually raises [Break], simulating a Ctrl-C) *)

val check_for_interrupt : unit -> unit
(** Use this function as a potential yield function. If {!interrupt} has been
    set, il will raise [Sys.Break]. *)

val set_interrupt_poll : (unit -> bool) option -> unit
(** [set_interrupt_poll (Some poll)] makes {!check_for_interrupt} call [poll]
    periodically (every 1000 calls) and raise [Sys.Break] if [poll ()] returns
    [true]. This is useful when no other thread can set {!interrupt}, e.g.
    when Rocq runs in a Web Worker (js_of_ocaml, wasm_of_ocaml) and the
    interruption request comes from shared memory. *)

val timeout : float -> ('a -> 'b) -> 'a -> ('b, Exninfo.info) result
(** [timeout n f x] tries to compute [Ok (f x)], and if it fails to do
    so before [n] seconds, returns [Error info] instead (where [info]
    contains the backtrace of the timeout exception). *)

type kilowords = { kilowords : Int64.t } [@@unboxed]

val alloc_limit : kilowords -> ('a -> 'b) -> 'a -> ('b * kilowords, Exninfo.info) result

(** Set a particular timeout function; warning, this is an internal
   API and it is scheduled to go away. *)
type timeout = { timeout : 'a 'b. float -> ('a -> 'b) -> 'a -> ('b,Exninfo.info) result }
val set_timeout : timeout -> unit

(** [protect_sigalrm f x] computes [f x], but if SIGALRM is received during that
    computation, the signal handler is executed only once the computation is
    terminated. Otherwise said, it makes the execution of [f] atomic w.r.t.
    handling of SIGALRM.

    This is useful for example to prevent the implementation of `Timeout` to
    interrupt I/O routines, generating ill-formed output.

*)
val protect_sigalrm : ('a -> 'b) -> 'a -> 'b
