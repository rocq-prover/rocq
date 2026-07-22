(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module WProof = AsyncTaskQueue.MakeWorker(Stm.ProofTask) ()
module WQuery = AsyncTaskQueue.MakeWorker(Stm.QueryTask) ()
module WTactic = AsyncTaskQueue.MakeWorker(Partac.TacTask) ()

let error s () =
  Format.eprintf "Usage: rocqworker --kind=[compile|repl|proof|query|tactic|nursery] $args@\ngot %s\n%!" s;
  exit 1

type kind =
  | Worker of { init : unit -> unit; loop : unit -> unit }
  | Compile
  | Repl
  | Nursery

let start main kind args = match kind with
  | Worker { init; loop } -> WorkerLoop.start ~init ~loop args
  | Compile -> Coqc.main args
  | Repl -> Coqtop.(start_coq coqtop_toplevel args)
  | Nursery -> Nursery.start main args

let rec main = function
  | [] -> error "no argument" ()
  | kind :: argv ->
    let kind =
      match kind with
      | "--kind=compile" -> Compile
      | "--kind=repl" -> Repl
      | "--kind=proof" -> Worker { init = WProof.init_stdout; loop = WProof.main_loop }
      | "--kind=query" -> Worker { init = WQuery.init_stdout; loop = WQuery.main_loop }
      | "--kind=tactic" -> Worker { init = WTactic.init_stdout; loop = WTactic.main_loop }
      | "--kind=nursery" -> Nursery
      | s -> error s ()
    in
    start main kind argv
