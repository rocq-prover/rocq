(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names

let scheme_map = Summary.ref GlobRef.Map_env.empty ~name:"Schemes"

let cache_one_scheme kind (gr,const) =
  scheme_map := GlobRef.Map_env.update gr (function
      | None -> Some (CString.Map.singleton kind const)
      | Some map -> Some (CString.Map.add kind const map))
      !scheme_map

let cache_scheme (kind,l) =
  cache_one_scheme kind l

let subst_one_scheme subst (gr,const) =
  (Globnames.subst_global_reference subst gr, Globnames.subst_global_reference subst const)

let subst_scheme (subst,(kind,l)) =
  (kind, subst_one_scheme subst l)

let inScheme : Libobject.locality * (string * (GlobRef.t * GlobRef.t)) -> Libobject.obj =
  let open Libobject in
  declare_object @@ object_with_locality "SCHEME"
    ~cache:cache_scheme
    ~subst:(Some subst_scheme)
    ~discharge:(fun x -> x)

let declare_scheme local kind (gr, _ as grcl) =
  let () = match local, gr with
  | (Libobject.Export | Libobject.SuperGlobal), GlobRef.VarRef id ->
    if Global.is_in_section gr then
      CErrors.user_err
        Pp.(str "Cannot register a non-local scheme for section variable "
            ++ Names.Id.print id
            ++ str "; use the #[local] attribute.")
  | _, _ -> ()
  in
  Lib.add_leaf (inScheme (local,(kind,grcl)))

let lookup_scheme kind gr = CString.Map.find kind (GlobRef.Map_env.find gr !scheme_map)

let lookup_scheme_opt kind gr =
  try Some (lookup_scheme kind gr) with Not_found -> None

let all_schemes () = !scheme_map
