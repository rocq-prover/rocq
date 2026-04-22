(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Tac2val
open Tac2ffi
open Tac2types

module Value = Tac2ffi

(** Make a representation with a dummy from function *)
let make_to_repr f = Tac2ffi.make_repr (fun _ -> assert false) f

(** More ML representations *)

let to_qhyp v = match Value.to_block v with
| (0, [| i |]) -> AnonHyp (Value.to_int i)
| (1, [| id |]) -> NamedHyp (CAst.make (Value.to_ident id))
| _ -> assert false

let qhyp = make_to_repr to_qhyp

let to_bindings = function
| ValInt 0 -> NoBindings
| ValBlk (0, [| vl |]) ->
  ImplicitBindings (Value.to_list Value.to_constr vl)
| ValBlk (1, [| vl |]) ->
  ExplicitBindings ((Value.to_list (fun p -> to_pair to_qhyp Value.to_constr p) vl))
| _ -> assert false

let bindings = make_to_repr to_bindings

let to_constr_with_bindings v = match Value.to_tuple v with
| [| c; bnd |] -> (Value.to_constr c, to_bindings bnd)
| _ -> assert false

let constr_with_bindings = make_to_repr to_constr_with_bindings

let val_format = Tac2dyn.Val.create "format"

let format = repr_ext val_format

let to_rewrite_success v : Rewrite.rewrite_result_info = match Value.to_tuple v with
| [| rel; rhs; prf |] ->
   { rew_rel = Value.to_constr rel;
     rew_to = Value.to_constr rhs;
     rew_prf = Value.to_constr prf }
| _ -> assert false

let to_rewrite_result v : Rewrite.rewrite_result = match v with
| ValBlk (0, [| s |]) ->  Success (to_rewrite_success s)
| ValInt 0 -> Identity
| ValInt 1 -> Fail
| _ -> assert false

let rewrite_result = make_to_repr to_rewrite_result
