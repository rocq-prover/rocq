(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Per-thread references, based on the thread-local-storage package *)

type 'a ref
val ref : 'a -> 'a ref
val (!) : 'a ref -> 'a
val (:=) : 'a ref -> 'a -> unit
val incr : int ref -> unit
