(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util

type type_transform =
  Environ.env -> Constr.types -> (Constr.types, Pp.t) result

type handler = {
  check : Conversion.conv_pb -> Environ.env ->
    Constr.types -> Constr.types -> (unit, Pp.t) result;
  prepare_source : type_transform option;
  prepare_target : type_transform option;
}

let handlers = ref String.Map.empty

let register ~id handler =
  if String.is_empty id then
    CErrors.user_err Pp.(str "An unsafe cast identifier cannot be empty.");
  if String.Map.mem id !handlers then
    CErrors.user_err Pp.(str "Unsafe cast " ++ qstring id ++ str " is already registered.");
  handlers := String.Map.add id handler !handlers

let find id =
  match String.Map.find_opt id !handlers with
  | Some handler -> handler
  | None ->
    CErrors.user_err Pp.(str "Unsafe cast " ++ qstring id ++ str " is not registered.")

let unwrap id = function
  | Ok x -> x
  | Error message ->
    CErrors.user_err Pp.(str "Unsafe cast " ++ qstring id ++ str ": " ++ message)

let check id pb env source target =
  unwrap id ((find id).check pb env source target)

let transform id f env ty = unwrap id (f env ty)
