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

module Key = struct

  type is_mutual = bool

  type t = (string list * UnivGen.QualityOrSet.t option * is_mutual)

  let compare (a : t) (b : t) =
    let a1, a2, a3 = a and b1, b2, b3 = b in
    let c = CList.compare String.compare a1 b1 in
    if c <> 0 then c
    else
      let c = Option.compare UnivGen.QualityOrSet.compare a2 b2 in
      if c <> 0 then c
      else Bool.compare a3 b3

  module Self = struct
    type nonrec t = t
    let compare = compare
  end

  let equal a b = compare a b = 0

  module Set = CSet.Make(Self)
  module Map = CMap.Make(Self)

end

let scheme_map = Summary.ref Indmap_env.empty ~name:"Schemes"

let cache_one_scheme kind (ind,const) =
  scheme_map := Indmap_env.update ind (function
      | None -> Some (Key.Map.singleton kind const)
      | Some map -> Some (Key.Map.add kind const map))
      !scheme_map

let cache_scheme (kind,l) =
  cache_one_scheme kind l

let subst_one_scheme subst (ind,const) =
  (* Remark: const is a def: the result of substitution is a constant *)
  (Mod_subst.subst_ind subst ind, Globnames.subst_global_reference subst const)

let subst_scheme (subst,(kind,l)) =
  (kind, subst_one_scheme subst l)

let inScheme : Libobject.locality * (Key.t * (inductive * GlobRef.t)) -> Libobject.obj =
  let open Libobject in
  declare_object @@ object_with_locality "SCHEME"
    ~cache:cache_scheme
    ~subst:(Some subst_scheme)
    ~discharge:(fun x -> x)

let declare_scheme local kind indcl =
  Lib.add_leaf (inScheme (local,(kind,indcl)))

let lookup_scheme kind ind = Key.Map.find kind (Indmap_env.find ind !scheme_map)

let all_schemes () = !scheme_map
