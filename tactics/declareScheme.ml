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

let scheme_map = Summary.ref Indmap_env.empty ~name:"Schemes"

let cache_one_scheme kind (ind,const) =
  scheme_map := Indmap_env.update ind (function
      | None -> Some (CString.Map.singleton kind const)
      | Some map -> Some (CString.Map.add kind const map))
      !scheme_map

let cache_scheme (kind,l) _sum =
  cache_one_scheme kind l

let subst_one_scheme subst (ind,const) =
  (* Remark: const is a def: the result of substitution is a constant *)
  (Mod_subst.subst_ind subst ind, Globnames.subst_global_reference subst const)

let subst_scheme _sum subst (kind,l) =
  (kind, subst_one_scheme subst l)

let inScheme : Libobject.locality * (string * (inductive * GlobRef.t)) -> Libobject.obj =
  let open Libobject in
  Interp.declare_object @@ object_with_locality "SCHEME"
    ~cache:cache_scheme
    ~subst:(Some subst_scheme)
    ~discharge:(fun _ x -> x)

let declare_scheme sum local kind indcl =
  Lib.Interp.add_leaf sum (inScheme (local,(kind,indcl)))

let lookup_scheme kind ind = CString.Map.find kind (Indmap_env.find ind !scheme_map)

let all_schemes () = !scheme_map
