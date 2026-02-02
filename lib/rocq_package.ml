(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type t = {
  name : string;
  dir : string;
  logpath : string;
}

let resolve : string list -> t list = fun ps ->
  match ps with [] -> [] | _ ->
  let ps =
    try Findlib.package_deep_ancestors [] ps with
    | Findlib.No_such_package (p, _) ->
      CErrors.user_err Pp.(str "Failed to locate package " ++ str p)
    | Findlib.Package_loop p ->
      CErrors.user_err Pp.(str "Dependency loop on package: " ++ str p)
  in
  let query p =
    let p =
      let open Fl_package_base in
      try Fl_package_base.query p with
      | No_such_package (p, info) ->
        CErrors.user_err Pp.(str "Failed to query package: " ++ str p)
    in
    try
      let logpath = Fl_metascanner.lookup "rocqpath" [] p.package_defs in
      let dir = Filename.concat (p.Fl_package_base.package_dir) "rocq.d" in
      let name = p.Fl_package_base.package_name in
      Some {name; dir; logpath}
    with Not_found -> None
  in
  List.filter_map query ps
