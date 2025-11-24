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
open Goptions
open Vernacexpr

let vernac_set_option sum ~locality ~stage key opt =
  match opt with
  | OptionUnset -> unset_option_value_gen ~locality stage sum key
  | OptionSetString s -> set_string_option_value_gen ~locality stage sum key s
  | OptionSetInt n -> set_int_option_value_gen ~locality stage sum key (Some n)
  | OptionSetTrue -> set_bool_option_value_gen ~locality stage sum key true

let warn_set_append_deprecated =
  CWarnings.create ~name:"set-append-deprecated" ~category:Deprecation.Version.v9_1
    Pp.(fun () -> str "Set ... Append is not supported.")

let vernac_set_option sum ~locality ~stage table v =
  let table =
    if String.equal "Append" (List.last table) then begin
      let table = List.drop_last table in
      let () = match table with
        | ["Warnings"]|["Debug"] -> ()
        | _ ->
          CErrors.user_err
            Pp.(str "Set ... Append not allowed with " ++ prlist_with_sep spc str table ++ str ".")
      in
      warn_set_append_deprecated ();
      table
    end
    else table
  in
  vernac_set_option sum ~locality ~stage table v

let vernac_add_option sum local =
  let env = Global.env() in
  iter_table { aux = fun table x -> table.add sum env local x }

let vernac_remove_option sum local =
  let env = Global.env() in
  iter_table { aux = fun table x -> table.remove sum env local x }

let vernac_mem_option = iter_table { aux = fun table x -> table.mem (Global.env()) x}

let vernac_print_option sum key =
  try (get_ref_table key).print ()
  with Not_found ->
  try (get_string_table key).print ()
  with Not_found ->
  try print_option_value sum key
  with Not_found -> error_undeclared_key key
