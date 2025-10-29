(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp

module QGlobal = struct
  open Names

  type t = {
    library : DirPath.t;
    id : Id.t
  }

  let make library id = { library ; id }

  let repr x = (x.library, x.id)

  let equal u1 u2 =
    Id.equal u1.id u2.id &&
    DirPath.equal u1.library u2.library

  let hash u = Hashset.Combine.combine (Id.hash u.id) (DirPath.hash u.library)

  let compare u1 u2 =
    let c = Id.compare u1.id u2.id in
    if c <> 0 then c
    else
      DirPath.compare u1.library u2.library

  let to_string { library = d ; id } =
    DirPath.to_string d ^ "." ^ Id.to_string id
end

module QVar =
struct
  type repr =
    | Var of int
    | Unif of string * int
    | Global of QGlobal.t
  type t = repr

  let make_var n = Var n

  let make_unif s n = Unif (s,n)

  let make_global id = Global id

  let var_index = function
    | Var q -> Some q
    | Unif _ -> None
    | Global _ -> None

  let hash = function
    | Var q -> Hashset.Combine.combinesmall 1 q
    | Unif (s,q) -> Hashset.Combine.(combinesmall 2 (combine (CString.hash s) q))
    | Global id -> Hashset.Combine.combinesmall 3 (QGlobal.hash id)

  module Hstruct = struct
    type nonrec t = t

    open Hashset.Combine

    let hashcons = function
      | Var qv as q -> combinesmall 1 qv, q
      | Unif (s,i) as q ->
        let hs, s' = CString.hcons s in
        combinesmall 2 (combine hs i), if s == s' then q else Unif (s',i)
      | Global id as q -> combinesmall 3 (QGlobal.hash id), q

    let eq a b =
      match a, b with
      | Var a, Var b -> Int.equal a b
      | Unif (sa, ia), Unif (sb, ib) -> sa == sb && Int.equal ia ib
      | Global ida, Global idb -> QGlobal.equal ida idb
      | (Var _ | Unif _| Global _), _ -> false
  end

  module Hasher = Hashcons.Make(Hstruct)

  let hcons = Hashcons.simple_hcons Hasher.generate Hasher.hcons ()

  let compare a b = match a, b with
    | Var a, Var b -> Int.compare a b
    | Unif (s1,i1), Unif (s2,i2) ->
      let c = Int.compare i1 i2 in
      if c <> 0 then c
      else CString.compare s1 s2
    | Global ida, Global idb -> QGlobal.compare ida idb
    | Var _, _ -> -1
    | _, Var _ -> 1
    | Unif _, _ -> -1
    | _, Unif _ -> 1

  let equal a b = match a, b with
    | Var a, Var b ->  Int.equal a b
    | Unif (s1,i1), Unif (s2,i2) ->
      Int.equal i1 i2 && CString.equal s1 s2
    | Global ida, Global idb -> QGlobal.equal ida idb
    | (Var _| Unif _ | Global _), _ -> false

  let to_string = function
    | Var q -> Printf.sprintf "β%d" q
    | Unif (s,q) ->
      let s = if CString.is_empty s then "" else s^"." in
      Printf.sprintf "%sα%d" s q
    | Global id -> Printf.sprintf "γ%s" (QGlobal.to_string id)

  let raw_pr q = Pp.str (to_string q)

  let repr x = x
  let of_repr x = x

  let is_unif = function
    | Unif _ -> true
    | (Var _ | Global _) -> false

  module Self = struct type nonrec t = t let compare = compare end
  module Set = CSet.Make(Self)
  module Map = CMap.Make(Self)
end

type constant = QProp | QSProp | QType
type t = QVar of QVar.t | QConstant of constant
type quality = t

let var i = QVar (QVar.make_var i)
let global sg = QVar (QVar.make_global sg)

let var_index = function
  | QVar q -> QVar.var_index q
  | QConstant _ -> None

module Constants = struct
  let equal a b = match a, b with
    | QProp, QProp | QSProp, QSProp | QType, QType -> true
    | (QProp | QSProp | QType), _ -> false

  let compare a b = match a, b with
    | QSProp, QSProp -> 0
    | QSProp, _ -> -1
    | _, QSProp -> 1
    | QProp, QProp -> 0
    | QProp, _ -> -1
    | _, QProp -> 1
    | QType, QType -> 0

  let to_string = function
    | QProp -> "Prop"
    | QSProp -> "SProp"
    | QType -> "Type"

  let pr q = str (to_string q)

  let hash = function
    | QSProp -> 0
    | QProp -> 1
    | QType -> 2
end

let equal a b = match a, b with
  | QVar a, QVar b -> QVar.equal a b
  | QConstant a, QConstant b -> Constants.equal a b
  | (QVar _ | QConstant _), _ -> false

let is_qsprop s = equal s (QConstant QSProp)
let is_qprop s = equal s (QConstant QProp)
let is_qtype s = equal s (QConstant QType)
let is_qvar s = match s with QVar _ -> true | _ -> false
let is_qconst s = match s with QConstant _ -> true | _ -> false
let is_qglobal s = match s with QVar (QVar.Global _) -> true | _ -> false
let is_impredicative s = is_qprop s || is_qsprop s

let compare a b = match a, b with
  | QVar a, QVar b -> QVar.compare a b
  | QVar _, _ -> -1
  | _, QVar _ -> 1
  | QConstant a, QConstant b -> Constants.compare a b

let all_constants = [QConstant QSProp; QConstant QProp; QConstant QType]
let all = var 0 :: all_constants

let pr prv = function
  | QVar v -> prv v
  | QConstant q -> Constants.pr q

let raw_pr q = pr QVar.raw_pr q

let hash = let open Hashset.Combine in function
  | QConstant q -> Constants.hash q
  | QVar q -> combinesmall 3 (QVar.hash q)

let subst f = function
  | QConstant _ as q -> q
  | QVar qv as q ->
     match f qv with
     | QConstant _ as q -> q
     | QVar qv' as q' ->
        if qv == qv' then q else q'

let subst_fn m v =
  match QVar.Map.find_opt v m with
  | Some v -> v
  | None -> QVar v

module Hstruct = struct
  type nonrec t = t

  let hashcons = function
    | QConstant c as q -> Constants.hash c, q
    | QVar qv as q ->
       let hqv, qv' = QVar.hcons qv in
       Hashset.Combine.combinesmall 3 hqv, if qv == qv' then q else QVar qv'

  let eq a b =
    match a, b with
    | QVar a, QVar b -> a == b
    | QVar _, _ -> false
    | (QConstant _), _ -> equal a b
end

module Hasher = Hashcons.Make(Hstruct)

let hcons = Hashcons.simple_hcons Hasher.generate Hasher.hcons ()

let qsprop = snd @@ hcons (QConstant QSProp)
let qprop = snd @@ hcons (QConstant QProp)
let qtype = snd @@ hcons (QConstant QType)

module Self = struct type nonrec t = t let compare = compare end
module Set = CSet.Make(Self)
module Map = CMap.Make(Self)

type 'q pattern =
  | PQVar of 'q | PQConstant of constant

let pattern_match ps s qusubst =
  match ps, s with
  | PQConstant qc, QConstant qc' -> if Constants.equal qc qc' then Some qusubst else None
  | PQVar qio, q -> Some (Partial_subst.maybe_add_quality qio q qusubst)
  | PQConstant _, QVar _ -> None

let to_string = function
  | QConstant q -> Constants.to_string q
  | QVar q -> QVar.to_string q

module ElimConstraint = struct
  type kind = Equal | ElimTo

  let eq_kind : kind -> kind -> bool = (=)
  let compare_kind : kind -> kind -> int = Stdlib.compare

  let hash_kind = function
    | Equal -> 0
    | ElimTo -> 1

  let pr_kind = function
    | Equal -> str "="
    | ElimTo -> str "~>"

  type nonrec t = t * kind * t

  let equal (a,k,b) (a',k',b') =
    eq_kind k k' && equal a a' && equal b b'

  let compare (a,k,b) (a',k',b') =
    let c = compare_kind k k' in
    if c <> 0 then c
    else
      let c = compare a a' in
      if c <> 0 then c
      else compare b b'

  let pr prq (a,k,b) =
    hov 1 (pr prq a ++ spc() ++ pr_kind k ++ spc() ++ pr prq b)

  let raw_pr x = pr QVar.raw_pr x

  module Hstruct = struct
    type nonrec t = t

    let hashcons (q1,k,q2) =
      let hq1, q1 = hcons q1 in
      let hq2, q2 = hcons q2 in
      Hashset.Combine.(combinesmall (hash_kind k) (combine hq1 hq2)), (q1,k,q2)

    let eq (q1,k,q2) (q1',k',q2') =
      eq_kind k k' && q1 == q1' && q2 == q2'
  end

  module Hasher = Hashcons.Make(Hstruct)

  let hcons = Hashcons.simple_hcons Hasher.generate Hasher.hcons ()
end

module ElimConstraints =
struct
  module S = Stdlib.Set.Make(ElimConstraint)
  include S

  let pr prv c =
    v 0 (prlist_with_sep spc (fun (u1,op,u2) ->
      hov 0 (pr prv u1 ++ ElimConstraint.pr_kind op ++ pr prv u2))
           (elements c))

  module HConstraints = CSet.Hashcons(ElimConstraint)(struct
      type t = ElimConstraint.t
      let hcons = ElimConstraint.hcons
    end)

  let hcons = Hashcons.simple_hcons HConstraints.generate HConstraints.hcons ()
end

module QCumulConstraint = struct
  type kind = Eq | Leq

  let eq_kind : kind -> kind -> bool = (=)
  let compare_kind : kind -> kind -> int = Stdlib.compare

  let pr_kind (c : kind) = match c with
    | Eq -> Pp.str "="
    | Leq -> Pp.str "<="

  type t = quality * kind * quality

  let trivial ((a,(Eq|Leq),b) : t) = equal a b

  let equal (a,k,b) (a',k',b') =
    eq_kind k k' && equal a a' && equal b b'

  let compare (a,k,b) (a',k',b') =
    let c = compare_kind k k' in
    if c <> 0 then c
    else
      let c = compare a a' in
      if c <> 0 then c
      else compare b b'

  let pr prq (a,k,b) =
    let open Pp in
    hov 1 (pr prq a ++ spc() ++ pr_kind k ++ spc() ++ pr prq b)

  let raw_pr x = pr QVar.raw_pr x
end

module QCumulConstraints = struct include CSet.Make(QCumulConstraint)
  let pr prq c =
    let open Pp in
    v 0 (prlist_with_sep spc (fun (u1,op,u2) ->
      hov 0 (pr prq u1 ++ QCumulConstraint.pr_kind op ++ pr prq u2))
       (elements c))

  let trivial = for_all QCumulConstraint.trivial
end
