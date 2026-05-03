(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Keys for unification and indexing *)

open Names
open Constr
open Libobject
open Globnames

type key =
  | KGlob of GlobRef.t
  | KLam
  | KLet
  | KProd
  | KSort
  | KCase
  | KFix
  | KCoFix
  | KRel
  | KInt
  | KFloat
  | KString
  | KArray

module KeyOrdered = struct
  type t = key

  let hash gr =
    match gr with
    | KGlob gr -> 9 + GlobRef.UserOrd.hash gr
    | KLam -> 0
    | KLet -> 1
    | KProd -> 2
    | KSort -> 3
    | KCase -> 4
    | KFix -> 5
    | KCoFix -> 6
    | KRel -> 7
    | KInt -> 8
    | KFloat -> 9
    | KString -> 10
    | KArray -> 11

  let compare gr1 gr2 =
    match gr1, gr2 with
    | KGlob gr1, KGlob gr2 -> GlobRef.UserOrd.compare gr1 gr2
    | _, KGlob _ -> -1
    | KGlob _, _ -> 1
    | k, k' -> Int.compare (hash k) (hash k')

  let equal k1 k2 =
    match k1, k2 with
    | KGlob gr1, KGlob gr2 -> GlobRef.UserOrd.equal gr1 gr2
    | _, KGlob _ -> false
    | KGlob _, _ -> false
    | k, k' -> k == k'
end

module Keymap = HMap.Make(KeyOrdered)

(* Mapping structure for references to be considered equivalent *)

let keys = Summary.ref Keymap.empty ~name:"Keys_decl"

let add_kv k ki v vi m =
  Keymap.update k (Option.cata (fun m -> Some (Keymap.add v (ki, vi) m)) (Some (Keymap.singleton v (ki, vi)))) m

let add_keys k ki v vi =
  keys := add_kv k ki v vi (add_kv v vi k ki !keys)

let equiv_keys k k' =
  if k == k' || KeyOrdered.equal k k' then Some ((0, 0)) else
  try Some (Keymap.find k' (Keymap.find k !keys))
  with Not_found -> None

let mkKGlob env gr = KGlob (Environ.QGlobRef.canonize env gr)

(** Registration of keys as an object *)

let load_keys _ (ref, refi, ref', ref'i) =
  add_keys ref refi ref' ref'i

let cache_keys o =
  load_keys 1 o

let subst_key subst k =
  match k with
  | KGlob gr -> mkKGlob (Global.env ()) (subst_global_reference subst gr)
  | _ -> k

let subst_keys (subst,(k, ki , k', k'i)) =
  (subst_key subst k, ki, subst_key subst k', k'i)

let discharge_key = function
  | KGlob (GlobRef.VarRef _ as g) when Global.is_in_section g -> None
  | x -> Some x

let discharge_keys (k, ki, k', k'i) =
  match discharge_key k, discharge_key k' with
  | Some x, Some y -> Some (x, ki, y, k'i)
  | _ -> None

type key_obj = key * int * key * int

let inKeys : key_obj -> obj =
  declare_object @@ superglobal_object "KEYS"
    ~cache:cache_keys
    ~subst:(Some subst_keys)
    ~discharge:discharge_keys

let declare_equiv_keys ref refi ref' ref'i =
  Lib.add_leaf (inKeys (ref, refi, ref', ref'i))

let constr_key env kind c =
  try
    let rec aux k =
      match kind k with
      | Const (c, _) -> mkKGlob env (GlobRef.ConstRef c)
      | Ind (i, u) -> mkKGlob env (GlobRef.IndRef i)
      | Construct (c,u) -> mkKGlob env (GlobRef.ConstructRef c)
      | Var id -> mkKGlob env (GlobRef.VarRef id)
      | App (f, _) -> aux f
      | Proj (p, _, _) -> mkKGlob env (GlobRef.ConstRef (Projection.constant p))
      | Cast (p, _, _) -> aux p
      | Lambda _ -> KLam
      | Prod _ -> KProd
      | Case _ -> KCase
      | Fix _ -> KFix
      | CoFix _ -> KCoFix
      | Rel _ -> KRel
      | Meta _ -> raise Not_found
      | Evar _ -> raise Not_found
      | Sort _ -> KSort
      | LetIn _ -> KLet
      | Int _ -> KInt
      | Float _ -> KFloat
      | String _ -> KString
      | Array _ -> KArray
    in Some (aux c)
  with Not_found -> None

open Pp

let pr_key pr_global k =
  let open Pp in
  match k with
  | KGlob gr -> pr_global gr
  | KLam -> str"Lambda"
  | KLet -> str"Let"
  | KProd -> str"Product"
  | KSort -> str"Sort"
  | KCase -> str"Case"
  | KFix -> str"Fix"
  | KCoFix -> str"CoFix"
  | KRel -> str"Rel"
  | KInt -> str"Int"
  | KFloat -> str"Float"
  | KString -> str"String"
  | KArray -> str"Array"

let pr_keyset pr_global v =
  prlist_with_sep spc (fun (k, (i, i')) -> pr_key pr_global k ++ str "(" ++ int i ++ str ", " ++ int i' ++ str ")") (Keymap.bindings v)

let pr_mapping pr_global k v =
  pr_key pr_global k ++ str" <-> " ++ pr_keyset pr_global v

let pr_keys pr_global =
  Keymap.fold (fun k v acc -> pr_mapping pr_global k v ++ fnl () ++ acc) !keys (mt())
