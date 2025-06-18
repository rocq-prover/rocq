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

module T = Thread_local_storage
type nonrec 'a ref = 'a T.t

let ref v = let r = T.create () in T.set r v; r
let (!) r = T.get_exn r
let (:=) r v = T.set r v
let incr r = T.(set r ((get_exn r) + 1))
