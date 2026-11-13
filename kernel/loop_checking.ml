open Univ

let debug_loop_checking_invariants_flag, debug_loop_checking_invariants = CDebug.create_full ~name:"loop-checking-invariants" ()
let _debug_loop_checking_flag, debug_loop_checking = CDebug.create_full ~name:"loop-checking" ()
let _debug_loop_checking_set_can_flag, debug_loop_checking_set_can = CDebug.create_full ~name:"loop-checking-set-can" ()
let _debug_loop_checking_minimize_flag, debug_loop_checking_minimize = CDebug.create_full ~name:"loop-checking-minimize" ()
let debug_loop_checking_merged_flag, _debug_loop_checking_merged = CDebug.create_full ~name:"loop-checking-merged" ()

module Index :
sig
  type t
  val equal : t -> t -> bool
  val compare : t -> t -> int
  module Set : Set.S with type elt = t
  module Map : CMap.ExtS with type key = t and module Set := Set
  type table
  val empty : table
  val fresh : Level.t -> table -> t * table
  val mem : Level.t -> table -> bool
  val find : Level.t -> table -> t
  val repr : t -> table -> Level.t
  val dom : table -> Level.Set.t
  (* val hash : t -> int *)
end =
struct
  type t = int
  let equal = Int.equal
  let compare = Int.compare
  module Set = Int.Set
  module Map = Int.Map

  type table = {
    tab_len : int;
    tab_fwd : Level.t Int.Map.t;
    tab_bwd : int Level.Map.t
  }

  let empty = {
    tab_len = 0;
    tab_fwd = Int.Map.empty;
    tab_bwd = Level.Map.empty;
  }
  let mem x t = Level.Map.mem x t.tab_bwd
  let find x t = Level.Map.find x t.tab_bwd
  let repr n t = Int.Map.find n t.tab_fwd

  let fresh x t =
    let () = assert (not @@ mem x t) in
    let n = t.tab_len in
    n, {
      tab_len = n + 1;
      tab_fwd = Int.Map.add n x t.tab_fwd;
      tab_bwd = Level.Map.add x n t.tab_bwd;
    }

  let dom t = Level.Map.domain t.tab_bwd

  (* let hash x = x *)
end

module PMap = Index.Map

module NeList =
struct

  type 'a t =
    | Tip of 'a
    | Cons of 'a * 'a t

  let tip x = Tip x
  (* let cons x xs = Cons (x, xs) *)

  let map f (x : 'a t) : 'b t =
    let rec aux l =
      match l with
      | Tip x -> Tip (f x)
      | Cons (x, xs) ->
        let x' = f x in
        let xs' = aux xs in
        Cons (x', xs')
    in aux x

  let fold (f : 'a -> 'b -> 'b) (x : 'a t) (acc : 'b) : 'b =
    let rec aux acc l =
      match l with
      | Tip x -> f x acc
      | Cons (hd, tl) -> aux (f hd acc) tl
    in aux acc x

  let fold_ne (f : 'a -> 'b -> 'b) (g : 'a -> 'b) (x : 'a t) : 'b =
    let rec aux l =
      match l with
      | Tip x -> g x
      | Cons (hd, tl) -> f hd (aux tl)
    in aux x

  let fold_map (f : 'a -> 'b -> 'a * 'b) (x : 'a t) (acc : 'b) : 'a t * 'b =
    let rec aux acc l =
      match l with
      | Tip x -> let x', res = f x acc in Tip x', res
      | Cons (hd, tl) -> let hd', res = f hd acc in
        let tl', res = aux res tl in
        Cons (hd', tl'), res
    in aux acc x

  let iter f x =
    let rec aux l =
      match l with
      | Tip x -> f x
      | Cons (hd, tl) -> f hd; aux tl
    in aux x

  let for_all f x =
    let rec aux l =
      match l with
      | Tip x -> f x
      | Cons (hd, tl) -> f hd && aux tl
    in aux x

  let exists f x =
    let rec aux l =
      match l with
      | Tip x -> f x
      | Cons (hd, tl) -> f hd || aux tl
    in aux x

  let equal f x y =
    let rec aux l l' =
      match l, l' with
      | Tip x, Tip y -> f x y
      | Cons _, Tip _ -> false
      | Tip _, Cons _ -> false
      | Cons (hd, tl), Cons (hd', tl') ->
        f hd hd' && aux tl tl'
    in aux x y

  let compare f x y =
    let rec aux l l' =
      match l, l' with
      | Tip x, Tip y -> f x y
      | Cons _, Tip _ -> 1
      | Tip _, Cons _ -> -1
      | Cons (hd, tl), Cons (hd', tl') ->
        match f hd hd' with
        | 0 -> aux tl tl'
        | c -> c
    in aux x y

  let rec of_list = function
    | [] -> assert false
    | [hd] -> Tip hd
    | hd :: tl -> Cons (hd, of_list tl)

  let rec to_list = function
    | Tip hd -> [hd]
    | Cons (hd, tl) -> hd :: to_list tl

  let rec append xs ys =
    match xs with
    | Tip x -> Cons (x, ys)
    | Cons (x, xs) -> Cons (x, append xs ys)

  let map_splice (f : 'a -> 'a t option) (l : 'a t) : 'a t =
    let rec aux l =
      match l with
      | Tip x -> (match f x with Some l -> l | None -> l)
      | Cons (x, xs) ->
        match f x with
        | Some l -> append l (aux xs)
        | None -> Cons (x, aux xs)
    in aux l

  let concat_map (f : 'a -> 'b t) (l : 'a t) : 'b t =
    let rec aux l =
      match l with
      | Tip x -> f x
      | Cons (x, xs) -> append (f x) (aux xs)
    in aux l

  let find f l =
    let rec aux l =
      match l with
      | Tip (hd, v) -> if f hd then v else raise_notrace Not_found
      | Cons ((hd, v), tl) ->
        if f hd then v else aux tl
    in aux l

  let filter p l =
    let rec aux l =
      match l with
      | Tip x -> if p x then Some l else None
      | Cons (hd, tl) ->
        let phd = p hd in
        match aux tl with
        | None -> if phd then Some (Tip hd) else None
        | Some tl' ->
          if phd then
            if tl == tl' then Some l
            else Some (Cons (hd, tl'))
          else Some tl'
    in aux l

  type cmp =
    | Merge of bool (* false = use the left argument, true = use the right argument *)
    | Diff of int

  let add cmp x l =
    let rec aux l =
      match l with
      | Tip y ->
        (match cmp x y with
        | Merge false -> Tip x
        | Merge true -> l
        | Diff c ->
          if c <= 0 then Cons (x, l)
          else Cons (y, Tip x))
      | Cons (y, l') ->
        (match cmp x y with
         | Merge false -> Cons (x, l')
         | Merge true -> l
         | Diff c ->
            if c <= 0 then Cons (x, l)
            else let l'' = aux l' in
              if l'' == l' then l
              else Cons (y, l''))
    in aux l

  let add_opt x l =
    match l with
    | None -> Tip x
    | Some l -> Cons (x, l)
end

module SetWithCardinal (O:OrderedType.S) (S : Set.S with type elt = O.t) =
struct

  type t = { set : S.t; cardinal : int }

  let empty = { set = S.empty; cardinal = 0 }

  let is_empty s = S.is_empty s.set
  let cardinal s = s.cardinal

  let add x ({set; cardinal} as s) =
    let set' = S.add x set in
    if set' == set then s
    else { set = set'; cardinal = cardinal + 1}

  let singleton x = add x empty

  let mem x s = S.mem x s.set
  let remove x ({set; cardinal} as s) =
    let set' = S.remove x set in
    if set' == set then s
    else { set = set'; cardinal = cardinal - 1}

  let union s {set; _} = S.fold add set s

  let fold f s = S.fold f s.set

  let elements s = S.elements s.set

  let map f s =
    let s' = S.map f s.set in
    if s' == s.set then s
    else { set = s'; cardinal = S.cardinal s' } (* Cardinal might change if f maps two elements to the same *)

  let exists p s = S.exists p s.set

  let iter f s = S.iter f s.set

  let partition f (s : t) =
    let left = ref 0 and right = ref 0 in
    let f x =
      let res = f x in
      if res then (incr left; res)
      else (incr right; res)
    in
    let l, r = S.partition f s.set in
    { set = l; cardinal = !left }, { set = r; cardinal = !right }

  let choose s = S.choose s.set

  let filter_map f s =
    let s' = S.filter_map f s.set in
    if s' == s.set then s
    else { set = s'; cardinal = S.cardinal s' }

  let filter f s =
    let s' = S.filter f s.set in
    if s' == s.set then s
    else { set = s'; cardinal = S.cardinal s' }
end

module type TypeWithCardinal =
sig
  type t
  val cardinal : t -> int
end

(* The cardinal of a map is the sum of the cardinals of its values *)
module MapWithCardinal (O : OrderedType.S) (T : TypeWithCardinal) =
struct
  module M = Map.Make(O)
  type t = { map : T.t M.t; cardinal : int }

  let empty = { map = M.empty; cardinal = 0 }
  let is_empty m = M.is_empty m.map

  let cardinal_of x m = match M.find_opt x m.map with
    | Some v -> T.cardinal v
    | None -> 0

  let add x k m =
    let m' = M.add x k m.map in
    if m' == m.map then m
    else { map = m'; cardinal = m.cardinal - cardinal_of x m + T.cardinal k }

  let singleton x k = add x k empty

  let fold f m = M.fold f m.map
  let cardinal m = m.cardinal

  let update x f {map;cardinal} =
    let cardinal = ref cardinal in
    let fn x =
      let x' = f x in
      match x, x' with
      | None, Some m' -> cardinal := !cardinal + T.cardinal m'; x'
      | None, None -> x'
      | Some x, None -> cardinal := !cardinal - T.cardinal x; x'
      | Some x, Some y ->
        cardinal := !cardinal - T.cardinal x + T.cardinal y; x'
    in
    let m' = M.update x fn map in
    { map = m'; cardinal = !cardinal}

  let compute_cardinal m' =
    M.fold (fun _ v acc -> acc + T.cardinal v) m' 0

  let exists f m = M.exists f m.map
  let iter f m = M.iter f m.map

  let filter_map f m =
    let m' = M.filter_map f m.map in
    { map = m'; cardinal = compute_cardinal m' }

  let find x m = M.find x m.map
  let find_opt x m = M.find_opt x m.map
end

module Premises =
struct

  module Premise =
  struct
    type t = Index.t * int

    let equal x y : bool =
      let (idx, k) = x in
      let (idx', k') = y in
      if Index.equal idx idx' then
        Int.equal k k'
      else false

    let compare x y : int =
      let (idx, k) = x in
      let (idx', k') = y in
      match Index.compare idx idx' with
      | 0 -> Int.compare k k'
      | x -> x

    let incl x y : NeList.cmp =
      let (idx, k) = x in
      let (idx', k') = y in
      match Index.compare idx idx' with
      | 0 -> NeList.Merge (k <= k')
      | x -> NeList.Diff x
  end

  open NeList

  type t = Premise.t NeList.t

  let fold = NeList.fold

  let fold_ne = NeList.fold_ne

  let iter = NeList.iter
  let for_all = NeList.for_all
  let exists = NeList.exists
  (* let _add prem (x : t) : t = CList.merge_set Premise.compare [prem] x *)
  (* let _union (x : t) (y : t) : t = CList.merge_set Premise.compare x y *)
  let compare : t -> t -> int = NeList.compare Premise.compare
  let equal : t -> t -> bool = NeList.equal Premise.equal

  (* let of_list = NeList.of_list *)

  let to_list = NeList.to_list

  let pr pr_index_point prem =
    let open Pp in
    prlist_with_sep (fun () -> str ",") pr_index_point (to_list prem)

  let add : Premise.t -> t -> t = NeList.add Premise.incl

  let filter f l =
    NeList.filter f l

  let union (prems : t) (prems' : t) : t =
    fold add prems prems'

  let shift n p =
    if Int.equal n 0 then p
    else NeList.map (fun (x,k) -> (x, k + n)) p

  let subst idx u prems =
    let rec aux l =
      match l with
      | Tip (idx', k) ->
        if Index.equal idx idx' then shift k u
        else l
      | Cons ((idx', k) as prem, prems) ->
        if Index.equal idx idx' then union (shift k u) prems
        else let prems' = aux prems in
          if prems' == prems then l
          else add prem prems'
    in aux prems

end

let pr_clause pr_index_point (prems, concl) =
  let open Pp in
  hov 0 (Premises.pr pr_index_point prems ++ str " → " ++ pr_index_point concl)

type locality =
| Global
| Local

let pr_local local = let open Pp in
  match local with
  | Local -> spc () ++ str"(local)"
  | Global -> spc () ++ str"(global)"

type clause = Premises.t * (Index.t * int)

module ClausesOf = struct
  module ClauseInfo = struct
    type t = int * Premises.t

    let compare x y : int =
      let (k, prems) = x in
      let (k', prems') = y in
      match Int.compare k k' with
      | 0 -> Premises.compare prems prems'
      | x -> x

    let pr pr_index_point local concl (k, prem) =
      let open Pp in
      hov 0 (Premises.pr pr_index_point prem ++ str " → " ++ pr_index_point (concl, k) ++ pr_local local)
  end

  module ClauseSet = Set.Make(ClauseInfo)
  module SWC = SetWithCardinal(ClauseInfo)(ClauseSet)

  type t = { local : SWC.t; global : SWC.t }

  let empty = { local = SWC.empty; global = SWC.empty }
  let is_empty cls = SWC.is_empty cls.local && SWC.is_empty cls.global

  let add local cl cls =
    match local with
    | Local ->
      (* If the clause is already in the global set, don't add it to the local set *)
      if SWC.mem cl cls.global then cls
      else
        let local' = SWC.add cl cls.local in
        if local' == cls.local then cls
        else { cls with local = local' }
    | Global ->
      (* A global clause supersedes the same local one, e.g. when local universes are demoted *)
      let local' = SWC.remove cl cls.local in
      let global' = SWC.add cl cls.global in
      if global' == cls.global && local' == cls.local then cls
      else { local = local'; global = global' }

  (* Moves [cl] from the global to the local clauses, if it is global *)
  let localize cl cls =
    if SWC.mem cl cls.global then Some { local = SWC.add cl cls.local; global = SWC.remove cl cls.global }
    else None

  let pr pr_index_point local concl cls =
    let open Pp in
    v 0 (prlist_with_sep spc (ClauseInfo.pr pr_index_point local concl) (SWC.elements cls))

  let pr pr_index_point concl cls =
    let open Pp in
    pr pr_index_point Global concl cls.local ++ pr pr_index_point Local concl cls.global

  let shift n cls = if Int.equal n 0 then cls else SWC.map (fun (k, prems) -> (k + n, prems)) cls

  let shift n cls = { local = shift n cls.local; global = shift n cls.global }

  let iter f cls = SWC.iter f cls.local; SWC.iter f cls.global

  let map f cls = { local = SWC.map (f Local) cls.local; global = SWC.map (f Global) cls.global }

  let fold f cls acc = SWC.fold (f Local) cls.local (SWC.fold (f Global) cls.global acc)

  let fold_local f cls acc = SWC.fold f cls.local acc

  let has_local cls = not (SWC.is_empty cls.local)

  let filter f cls = { local = SWC.filter f cls.local; global = SWC.filter f cls.global }

  let filter_map f cls =
    let local = SWC.filter_map (f Local) cls.local in
    let global = SWC.filter_map (f Global) cls.global in
    if local == cls.local && global == cls.global then cls
    else { local; global }

  let mem cl cls = SWC.mem cl cls.local || SWC.mem cl cls.global

  let remove cl cls =
    let local = SWC.remove cl cls.local in
    let global = SWC.remove cl cls.global in
    if local == cls.local && global == cls.global then cls
    else { local; global }

  (* [replace cl f cls] replaces the clause [cl] of [cls], if present, by [f cl] in the same set, or
     removes it if [f cl] is [None], as [filter_map] would. The clause can be both local and global. *)
  let replace cl f cls =
    let replace s =
      if not (SWC.mem cl s) then s else
      let s' = SWC.remove cl s in
      match f cl with
      | None -> s'
      | Some cl' -> if cl' == cl then s else SWC.add cl' s'
    in
    let local = replace cls.local in
    let global = replace cls.global in
    if local == cls.local && global == cls.global then cls
    else { local; global }

  let union cls cls' =
    { local = SWC.union cls.local cls'.local; global = SWC.union cls.global cls'.global }

  let choose cls =
    if SWC.is_empty cls.global then SWC.choose cls.local
    else SWC.choose cls.global

  let cardinal cls = SWC.cardinal cls.local + SWC.cardinal cls.global

  let to_clauses local concl cls : (locality * clause) list =
    let to_clauses (conclk, prems) cls =
      let to_clauses (concl, k) cls = (local, (prems, (concl, conclk + k))) :: cls in
      NeList.fold to_clauses concl cls
    in
    SWC.fold to_clauses cls []

  let to_clauses concls cls =
    to_clauses Global concls cls.global @ to_clauses Local concls cls.local

end

module PartialClausesOf = struct
  module ClauseInfo = struct
    type t = int * Premises.t option

    let compare (x : t) (y : t) : int =
      let (k, prems) = x in
      let (k', prems') = y in
      match Int.compare k k' with
      | 0 -> Option.compare Premises.compare prems prems'
      | x -> x

    (* let of_list (k, prems) = (k, Premises.of_list prems) *)

    let pr pr_index_point prem concl (k, prems) =
      let open Pp in
      hov 0 (prlist_with_sep (fun () -> str ",") pr_index_point (prem :: Option.cata Premises.to_list [] prems)
        ++ str " → " ++ pr_index_point (concl, k))
  end

  module ClauseInfos = Set.Make (ClauseInfo)
  module SWC = SetWithCardinal(ClauseInfo)(ClauseInfos)
  include SWC

  let pr pr_index_point prem concl cls =
    let open Pp in
    v 0 (prlist_with_sep spc (ClauseInfo.pr pr_index_point prem concl) (elements cls))

  let shift n cls = if Int.equal n 0 then cls else map (fun (k, prems) -> (k + n, prems)) cls

end

type fwd_clause =
  { prems : PartialClausesOf.t;
    kprem : int;
    concl : Index.t }

module ForwardClauses =
struct
  module PMap = MapWithCardinal (Index) (PartialClausesOf)
  (** This type represents a map from conclusions to increments + premises,
     e.g [other -> concl + n] *)

  module IntMap = MapWithCardinal (Int) (PMap)
  (** [t] This type represents forward clauses [(_ + k, other -> concl + n)].
    The premises are necessarily non-empty, and the [(_ + k)] one is singled out.
    They are indexed by [k], then by the conlusion universe [concl] and finally
    by [n], in PartialClausesOf.t, which contains the potentially empty [other] premises.
    The cardinal is maintained for fast computations. *)
  type t = IntMap.t

  let add (cl : fwd_clause) (clauses : t) : t =
    if PartialClausesOf.is_empty cl.prems then clauses else
    IntMap.update cl.kprem
      (fun cls ->
        match cls with
        | None -> Some (PMap.singleton cl.concl cl.prems)
        | Some cls ->
          Some (PMap.update cl.concl
            (fun cls ->
              match cls with
              | None -> Some cl.prems
              | Some cls -> Some (PartialClausesOf.union cl.prems cls))
          cls))
      clauses

  let replace (cl : fwd_clause) (clauses : t) : t =
    IntMap.update cl.kprem
      (fun cls ->
        match cls with
        | None -> Some (PMap.singleton cl.concl cl.prems)
        | Some cls ->
          Some (PMap.add cl.concl cl.prems cls))
      clauses

  let filter_map (f : int -> Index.t -> PartialClausesOf.t -> PartialClausesOf.t option) clauses =
    IntMap.fold (fun k fwd acc ->
      let fwd = PMap.filter_map (f k) fwd in
      if PMap.is_empty fwd then acc else IntMap.add k fwd acc)
      clauses IntMap.empty

  (** [remove ~kprem concl cl cls] removes the partial clause [cl] of conclusion [concl] from
    the forward clauses [cls] of premise increment [kprem] *)
  let remove ~kprem concl cl (cls : t) : t =
    IntMap.update kprem (function
      | None -> None
      | Some pcls ->
        let pcls' = PMap.update concl (function
          | None -> None
          | Some cls -> let cls' = PartialClausesOf.remove cl cls in
            if PartialClausesOf.is_empty cls' then None else Some cls') pcls
        in
        if PMap.is_empty pcls' then None else Some pcls') cls

  let cardinal (cls : t) : int = IntMap.cardinal cls
  let empty = IntMap.empty
  let is_empty x = IntMap.is_empty x
  let singleton cl = add cl empty

  let fold (f : kprem:int -> concl:Index.t -> prems:PartialClausesOf.t -> 'a -> 'a) (cls : t) : 'a -> 'a =
    IntMap.fold (fun kprem cls acc ->
      PMap.fold (fun concl prems acc ->
        f ~kprem ~concl ~prems acc) cls acc)
      cls

  let exists (f : kprem:int -> concl:Index.t -> prems:PartialClausesOf.t -> bool) (cls : t) : bool =
    IntMap.exists (fun kprem cls ->
      PMap.exists (fun concl prems -> f ~kprem ~concl ~prems) cls)
      cls

  (** [mem ~kprem concl cl cls] is [true] iff the partial clause [cl] of conclusion [concl]
    is in the forward clauses [cls] of premise increment [kprem] *)
  let mem ~kprem concl cl (cls : t) =
    match IntMap.find_opt kprem cls with
    | None -> false
    | Some pcls ->
      match PMap.find_opt concl pcls with
      | None -> false
      | Some cls -> PartialClausesOf.mem cl cls

  (** [add_all cls cls'] adds the clauses [cls] to [cls'], in time logarithmic in the size of [cls']
    for each clause of [cls] (unlike [union]) *)
  let add_all (cls : t) (cls' : t) : t =
    fold (fun ~kprem ~concl ~prems acc -> add { kprem; concl; prems } acc) cls cls'

  let pr_clauses pr prem (cls : PMap.t) =
    let open Pp in
    PMap.fold (fun concl cls acc -> PartialClausesOf.pr pr prem concl cls ++ spc () ++ acc) cls (mt())

  let pr pr_prem prem (cls : t) =
    let open Pp in
    IntMap.fold
      (fun kprem cls acc -> pr_clauses pr_prem (prem, kprem) cls ++ acc)
      cls (mt ())

  let to_clauses u cls : clause list =
    let to_clause ~kprem ~concl ~prems cls =
      let to_clause (kconcl, prems) cls =
        match prems with
        | None -> (Premises.shift kprem u, (concl, kconcl)) :: cls
        | Some p -> (NeList.append (Premises.shift kprem u) p, (concl, kconcl)) :: cls
      in
      PartialClausesOf.fold to_clause prems cls
    in
    fold to_clause cls []

end

module PSet = SetWithCardinal(Index)(Index.Set)

(* Beware, do not use pointer equality, rather use the [canon] Index.t equality,
  as canonical nodes get updated clauses and values throughout the algorithms. *)
type canonical_node =
  { canon: Index.t;
    local: locality;
    rigid : bool; (* Prefer to maintain this canonical node when equating it with another *)
    value : int;
    clauses_bwd : ClausesOf.t; (* premises -> canon + k *)
    clauses_fwd : ForwardClauses.t (* canon + k, ... ->  concl + k' *) }

(* The substitution of a level [u], which is no longer a canonical node *)
type alias = {
  alias_prems : Premises.t; (* The universe [u] is equal to, always canonical *)
  alias_local : locality; (* The locality of [u] *)
  alias_local_eq : locality; (* The locality of the equation *)
  alias_rigid : bool; (* Whether [u] was rigid: only non-rigid aliases are substituted in terms *)
}

type model = {
  locality : locality;
  entries : canonical_node PMap.t; (* The canonical nodes *)
  subst : alias PMap.t; (* The substitution from levels to universes *)
  subst_deps : Index.Set.t PMap.t; (* For each canonical node, the levels whose substitution mentions it *)
  values : int PMap.t option; (* values, superseding the ones attached to canonical nodes if present *)
  canonical : int; (* Number of canonical nodes *)
  locals : Index.Set.t; (* Contains the canonical nodes which are local or have local clauses, and maybe
    other indices: they are checked again when used *)
  local_eqs : Index.Set.t; (* Contains the substituted levels whose substitution is local *)
  table : Index.table }

let set_local m = { m with locality = Local }

let empty_model = {
  locality = Global;
  entries = PMap.empty;
  subst = PMap.empty;
  subst_deps = PMap.empty;
  values = None;
  canonical = 0;
  locals = Index.Set.empty;
  local_eqs = Index.Set.empty;
  table = Index.empty
}

let empty = empty_model

let add_subst_deps w prems deps =
  NeList.fold (fun (idx, _) deps ->
      PMap.update idx (function
          | None -> Some (Index.Set.singleton w)
          | Some s -> Some (Index.Set.add w s)) deps)
    prems deps

let subst_deps_of subst =
  PMap.fold (fun w { alias_prems = prems; _ } deps -> add_subst_deps w prems deps) subst PMap.empty

let remove_subst_deps w prems deps =
  NeList.fold (fun (idx, _) deps ->
      PMap.update idx (function
          | None -> None
          | Some s ->
            let s = Index.Set.remove w s in
            if Index.Set.is_empty s then None else Some s) deps)
    prems deps

(** [remove_dominated_set index setidx prems] drops [Set + k] from [prems] when they also have a
  premise [b + k'] with [k <= k']: [Set] is below every universe, so it is never the maximum. The
  premises of clauses and substitutions are kept in that form, so that e.g. [max(Set, b)] is [b]. *)
let remove_dominated_set index setidx prems =
  match prems with
  | NeList.Tip _ -> prems
  | NeList.Cons _ ->
    let is_set (p, _) = Index.equal (index p) setidx in
    match NeList.fold (fun x acc -> if is_set x then Some (snd x) else acc) prems None with
    | None -> prems
    | Some kset ->
      if NeList.exists (fun (_, k as x) -> not (is_set x) && kset <= k) prems then
        Option.default prems (NeList.filter (fun x -> not (is_set x)) prems)
      else prems

(* [enter_equiv m u local v] makes the canonical node [u] an alias of the
   canonical premises [v]. The substitutions mentioning [u] are rewritten to
   mention [v] instead, so that the premises of the substitution stay
   canonical: normalizing a level then only takes a single lookup, instead of
   following chains of aliases whose length can grow linearly with the number
   of equations. *)
let enter_equiv m u local v =
  let setidx = Index.find Level.set m.table in
  let rigid = (PMap.find u m.entries).rigid in
  let v = remove_dominated_set Fun.id setidx v in
  let deps = PMap.find_opt u m.subst_deps in
  let subst_deps = PMap.remove u m.subst_deps in
  let subst, subst_deps = match deps with
    | None -> m.subst, subst_deps
    | Some ws ->
      Index.Set.fold (fun w (subst, subst_deps) ->
          let alias = PMap.find w subst in
          let prems = remove_dominated_set Fun.id setidx (Premises.subst u v alias.alias_prems) in
          PMap.add w { alias with alias_prems = prems } subst, add_subst_deps w v subst_deps)
        ws (m.subst, subst_deps)
  in
  { locality = m.locality;
    entries = PMap.remove u m.entries;
    subst = PMap.add u { alias_prems = v; alias_local = local; alias_local_eq = m.locality; alias_rigid = rigid } subst;
    subst_deps = add_subst_deps u v subst_deps;
    canonical = m.canonical - 1;
    values = Option.map (PMap.remove u) m.values;
    locals = m.locals;
    local_eqs = (match m.locality with Local -> Index.Set.add u m.local_eqs | Global -> m.local_eqs);
    table = m.table }

let change_node m n =
  let locals =
    if n.local == Local || ClausesOf.has_local n.clauses_bwd then Index.Set.add n.canon m.locals
    else m.locals
  in
  { m with entries = PMap.set n.canon n m.entries; locals }

exception Undeclared of Level.t

(* let _ = CErrors.register_handler *)
  (* (function Undeclared l -> Some Pp.(str"Undeclared universe level: " ++ Level.raw_pr l) | _ -> None) *)

(* canonical representative : we follow the Equiv links *)
let repr m u = PMap.find u m.entries

let repr_expr m (u, k) = (repr m u, k)

let repr_premises m p =
  NeList.map (repr_expr m) p

let rec canonical_repr m (u, k) =
  match PMap.find u m.entries with
  | can -> NeList.Tip (can, k)
  | exception Not_found ->
    match PMap.find u m.subst with
    | { alias_prems = p; _ } -> canonical_premises_repr m (Premises.shift k p)
    | exception Not_found -> raise (Undeclared (Index.repr u m.table))
and canonical_premises_repr m p =
  NeList.concat_map (canonical_repr m) p

let expr_of_can_premise m (can, k) = (Index.repr can.canon m.table, k)
let expr_of_premise m (idx, k) = (Index.repr idx m.table, k)

let univ_of_can_expr_list model u = Universe.unrepr (List.map (expr_of_can_premise model) u)

let univ_of_can_premises model u = Universe.unrepr (NeList.to_list (NeList.map (expr_of_can_premise model) u))

let univ_of_premises model u = Universe.unrepr (NeList.to_list (NeList.map (expr_of_premise model) u))

let normalize m l =
  match Index.find l m.table with
  | exception Not_found -> None
  | idx ->
    match PMap.find idx m.entries with
    | _can -> None (* Already in canonical form *)
    | exception Not_found ->
      match PMap.find idx m.subst with
      | { alias_prems = p; _ } -> Some (univ_of_premises m p) (* [p] is canonical *)
      | exception Not_found -> None

let refresh_can_expr m (u, k) = repr_expr m (u.canon, k)

let pr_expr = LevelExpr.pr Level.raw_pr

let pr_raw_index_point m idx =
  try pr_expr (Index.repr idx m.table, 0)
  with Not_found -> Pp.str"<point not in table>"

let pr_raw_index_point_expr m (idx, n) =
  try pr_expr (Index.repr idx m.table, n)
  with Not_found -> Pp.str"<point not in table>"

let pr_raw_premises m p =
  try match p with
    | NeList.Tip e -> pr_raw_index_point_expr m e
    | NeList.Cons _ -> Pp.(str"max(" ++ prlist_with_sep (fun () -> str ", ") (pr_raw_index_point_expr m) (NeList.to_list p) ++ str")")
  with Not_found -> Pp.str"<point not in table>"

let pr_index_point m (idx, n) =
  let (idx, k) = try let can = repr m idx in (can.canon, n) with Not_found -> (idx, n) in
  try pr_expr (Index.repr idx m.table, k)
  with Not_found -> Pp.str"<point not in table>"

let pr_clauses_of m = ClausesOf.pr (pr_index_point m)

let eq_expr (idxu, ku as u) (idxv, kv as v) =
  u == v || (Index.equal idxu idxv && Int.equal ku kv)

let eq_can_expr (canu, ku as u) (canv, kv as v) =
  u == v || (canu == canv && Int.equal ku kv)

let cons_opt_nelist tip rest =
  match rest with
  | None -> NeList.tip tip
  | Some l -> NeList.Cons (tip, l)

let pr_fwd_clause m prem (cls : ForwardClauses.t) =
  ForwardClauses.pr (pr_index_point m) prem cls

type t = model

let canonical_can_premises p =
  NeList.map (fun (can, k) -> (can.canon, k)) p

let pr_clause_idx m cl = pr_clause (pr_index_point m) cl

type can_premises = (canonical_node * int) NeList.t
type can_expr = canonical_node * int
type can_clause = can_premises * can_expr

type 'a canonical_result =
  | Trivial
  | Contradictory
  | Canonical of 'a

let simplify_can_premises setidx prems concl conclk =
  (* The result is sorted according to the order on the [canon] indices, mentioning each
     universe once with its largest increment, as built by [Premises.add], and without
     [Set + k] when another premise has an increment [k' >= k] (see [remove_dominated_set]) *)
  let rec insert ((prem, k) as x) prems =
    match prems with
    | NeList.Tip ((prem', k') as p) ->
      let c = Index.compare prem.canon prem'.canon in
      if Int.equal c 0 then if k <= k' then prems else NeList.Tip x
      else if c < 0 then NeList.Cons (x, prems)
      else NeList.Cons (p, NeList.Tip x)
    | NeList.Cons ((prem', k') as p, prems') ->
      let c = Index.compare prem.canon prem'.canon in
      if Int.equal c 0 then if k <= k' then prems else NeList.Cons (x, prems')
      else if c < 0 then NeList.Cons (x, prems)
      else
        let prems'' = insert x prems' in
        if prems' == prems'' then prems else NeList.Cons (p, prems'')
  in
  (* A premise [concl + k] makes the clause trivial if [k >= conclk], otherwise it can never
     be the maximum and is dropped: [concl + conclk <= max(concl + k, prems)] is equivalent to
     [concl + conclk <= max(prems)]. Without premises left, the clause is contradictory. *)
  let exception IsTrivial in
  let update ((prem, k) as x) acc =
    if Index.equal prem.canon concl.canon then
      if k >= conclk then raise_notrace IsTrivial else acc
    else match acc with
      | None -> Some (NeList.Tip x)
      | Some prems -> Some (insert x prems)
  in
  match NeList.fold update prems None with
  | exception IsTrivial -> Trivial
  | None -> Contradictory
  | Some prems -> Canonical (remove_dominated_set (fun can -> can.canon) setidx prems)

(** Simplify u <= max (Set, v) clauses to u <= v and filter away u <= ... u + n , ... clauses, always valid *)
let simplify_can_clause m ((prems, (concl, k as conclk)) : can_clause) : can_clause canonical_result =
  (* Filter out `Set` from max(Set, u) -> v constraints *)
  let setidx = Index.find Level.set m.table in
  (* Trivial ... u + k + n ... -> Set + k (k > 0) clause *)
  if concl.canon == setidx && NeList.exists (fun (_prem, k') -> k' >= k && k > 0) prems then
    Trivial
  else
    match simplify_can_premises setidx prems concl k with
    | Canonical prems -> Canonical (prems, conclk)
    | Trivial -> Trivial
    | Contradictory -> Contradictory

(** [sorted_premises prems] holds when [prems] is sorted according to the order on [Index.t],
  mentioning each universe once, as built by [Premises.add]. *)
let rec sorted_premises = function
  | NeList.Tip _ -> true
  | NeList.Cons ((idx, _), (NeList.Tip (idx', _) | NeList.Cons ((idx', _), _) as prems)) ->
    Index.compare idx idx' < 0 && sorted_premises prems

(** [is_trivial_clause setidx (prems, (concl, k))] holds when the clause is trivial,
  in the sense of [simplify_can_clause]. *)
let is_trivial_clause setidx (prems, (concl, k)) =
  Premises.exists (fun (prem, k') -> k' >= k && (Index.equal prem concl || (Index.equal concl setidx && k > 0))) prems

(** [simplify_clause setidx cl] simplifies the clause [cl] on canonical sorted premises as
  [simplify_can_clause]: if it is not trivial, its premises on its conclusion and [Set + k] below
  another premise are dropped. *)
let simplify_clause setidx (prems, (concl, k) as cl) =
  if is_trivial_clause setidx cl then Trivial
  else match Premises.filter (fun (idx, _) -> not (Index.equal idx concl)) prems with
    | None -> Contradictory
    | Some prems' ->
      let prems' = remove_dominated_set Fun.id setidx prems' in
      Canonical (if prems' == prems then cl else (prems', (concl, k)))

(** [fwd_premises prem kprem others] are the premises of the forward clause [prem + kprem, others -> _] *)
let fwd_premises prem kprem others =
  match others with
  | None -> NeList.Tip (prem, kprem)
  | Some others -> Premises.add (prem, kprem) others

let check_invariants ~(required_canonical:Level.t -> bool) model =
  let required_canonical u = required_canonical (Index.repr u model.table) in
  let n_canon = ref 0 in
  (* The clause [prems -> concl + k], stored in the [kind] clauses of [node], only mentions canonical universes,
     has sorted premises mentioning each universe once but not its conclusion, and is neither trivial
     nor contradictory *)
  let setidx = Index.find Level.set model.table in
  let check_clause kind node (prems, (concl, k) as cl) =
    let err msg =
      CErrors.user_err Pp.(str kind ++ str" clause " ++ pr_clause_idx model cl ++ str" of " ++
        pr_raw_index_point model node ++ spc () ++ msg)
    in
    let check_canonical idx =
      if not (PMap.mem idx model.entries) then
        err Pp.(str"mentions the non-canonical universe " ++ pr_raw_index_point model idx)
    in
    check_canonical concl;
    Premises.iter (fun (idx, _) -> check_canonical idx) prems;
    if Premises.exists (fun (idx, _) -> Index.equal idx concl) prems then
      err Pp.(str"mentions its conclusion in its premises");
    if not (sorted_premises prems) then
      err Pp.(str"has unsorted premises, or premises mentioning the same universe several times");
    if remove_dominated_set Fun.id setidx prems != prems then
      err Pp.(str"has a premise Set + k below another premise");
    let canprems = NeList.map (fun (idx, k) -> (repr model idx, k)) prems in
    match simplify_can_clause model (canprems, (repr model concl, k)) with
    | Trivial -> err Pp.(str"is trivial")
    | Contradictory -> err Pp.(str"is contradictory")
    | Canonical _ -> ()
  in
  PMap.iter (fun idx can ->
    assert (Index.equal idx can.canon);
    assert (Index.mem (Index.repr idx model.table) model.table);
    if (can.local == Local || ClausesOf.has_local can.clauses_bwd) && not (Index.Set.mem idx model.locals) then
      CErrors.user_err Pp.(pr_raw_index_point model idx ++ str" is local or has local clauses but is not in the local nodes");
    (* assert (PMap.mem idx model.values); *)
    ForwardClauses.fold (fun ~kprem ~concl ~prems () ->
      PartialClausesOf.iter (fun (kconcl, others) ->
        (* can + kprem, others -> concl + kconcl *)
        Option.iter (fun others ->
          if not (sorted_premises others) || Premises.exists (fun (idx, _) -> Index.equal idx can.canon) others then
            CErrors.user_err Pp.(str"Forward clause of " ++ pr_raw_index_point model can.canon ++
              str" has other premises " ++ Premises.pr (pr_index_point model) others ++
              str" that are unsorted, mention a universe several times or mention " ++
              pr_raw_index_point model can.canon))
          others;
        let prems = fwd_premises can.canon kprem others in
        check_clause "Forward" can.canon (prems, (concl, kconcl));
        (* Ensure it is registered as a backward clause of concl *)
        let conclcan = repr model concl in
        if not (ClausesOf.mem (kconcl, prems) conclcan.clauses_bwd) then
          CErrors.user_err Pp.(str"Forward clause " ++ pr_clause_idx model (prems, (concl, kconcl)) ++
            str" of " ++ pr_raw_index_point model can.canon ++
            str" is not registered as a backward clause of " ++ pr_raw_index_point model concl))
        prems) can.clauses_fwd ();
    let cls = can.clauses_bwd in
    ClausesOf.iter
      (fun (k, prems) ->
        (* prems -> can + k *)
        if not (k >= 0) then CErrors.user_err Pp.(str "A conclusion has negative weight") else ();
        check_clause "Backward" can.canon (prems, (can.canon, k));
        let check_prem (l, lk) =
          if not (lk >= 0) then CErrors.user_err Pp.(str "A premise has negative weight") else ();
          assert (PMap.mem l model.entries);
          let lcan = repr model l in
          (* Ensure this backward clause of shape [max(... l + lk ... ) -> can + k] is registered as a forward clause for the premise l *)
          match ForwardClauses.IntMap.find_opt lk lcan.clauses_fwd with
          | Some fwd ->
            ForwardClauses.PMap.exists (fun idx kprem ->
            (* kprem = { (kconcl, max ( ... l' + lk' ... )) } -> idx *)
            let can' = repr model idx in
            can' == can &&
            PartialClausesOf.exists (fun (k', prems') ->
              Int.equal k k' && Premises.equal prems (fwd_premises lcan.canon lk prems')) kprem)
              fwd
          | None -> false
        in
        Premises.iter
          (fun kprem -> if (check_prem kprem) then () else
          CErrors.user_err Pp.(str"Clause " ++
            pr_fwd_clause model (fst kprem)
            (ForwardClauses.singleton { concl = can.canon; kprem = (snd kprem);
              prems = PartialClausesOf.singleton (k, NeList.filter (fun x -> not (eq_expr kprem x)) prems) }) ++ str" is not registered as a forward clauses for "
            ++ pr_index_point model kprem ++ fnl () ++ str" prems = " ++ pr_clause_idx model (prems, (can.canon, k)))) prems) cls;
      incr n_canon) model.entries;
  PMap.iter (fun idx { alias_prems = u; alias_local_eq = local_eq; _ } ->
    if local_eq == Local && not (Index.Set.mem idx model.local_eqs) then
      CErrors.user_err Pp.(pr_raw_index_point model idx ++ str" has a local substitution but is not in the local ones");
    if not (sorted_premises u) then
      CErrors.user_err Pp.(str"The substitution of " ++ pr_raw_index_point model idx ++ str" by " ++
        pr_raw_premises model u ++ str" has unsorted premises, or premises mentioning the same universe several times");
    if remove_dominated_set Fun.id setidx u != u then
      CErrors.user_err Pp.(str"The substitution of " ++ pr_raw_index_point model idx ++ str" by " ++
        pr_raw_premises model u ++ str" has a premise Set + k below another premise");
    Premises.iter (fun (idx', k) ->
      assert (k >= 0);
      assert (PMap.mem idx' model.entries); (* The substitution is canonical *)
      assert (Index.Set.mem idx (PMap.find idx' model.subst_deps));
      assert (Index.mem (Index.repr idx' model.table) model.table)) u;
      (* The clauses should not mention aliases *)
    assert (not (required_canonical idx))) model.subst

let lift_opt f x y =
  match x, y with
  | Some x', Some y' -> Some (f x' y')
  | Some _, None -> x
  | None, Some _ -> y
  | None, None -> None

let max_opt = lift_opt max
let min_opt = lift_opt min

let model_max (m : model) : int option =
  match m.values with
  | None ->
    Some (PMap.fold (fun _ can acc -> max can.value acc) m.entries 0)
  | Some values ->
    PMap.fold (fun _ v acc -> max_opt (Some v) acc) values None

let model_min (m : model) : int option =
  match m.values with
  | None ->
    Some (PMap.fold (fun _ can acc -> min can.value acc) m.entries 0)
  | Some values ->
    PMap.fold (fun _ v acc -> min_opt (Some v) acc) values None

let clauses_cardinal (m : model) : int =
  PMap.fold (fun _ can acc -> acc + ClausesOf.cardinal can.clauses_bwd)
    m.entries 0

let without_bound (m : model) : int =
  PMap.fold (fun _ can acc ->
      let cls = can.clauses_bwd in
      if ClausesOf.is_empty cls then succ acc else acc)
    m.entries 0

let length_path_from m idx =
  let rec aux = function
    | None -> 0
    | Some { alias_prems = u; _ } ->
      succ (Premises.fold (fun (idx, _) acc ->
        max (aux (PMap.find_opt idx m.subst)) acc) u 0)
  in aux (PMap.find_opt idx m.subst)

let rec maximal_path m =
  PMap.fold (fun _ { alias_prems = u; _ } acc ->
    max (succ (maximal_premises_path m u)) acc) m.subst 0
and maximal_premises_path m p =
  Premises.fold (fun (idx, _) acc ->
    max (length_path_from m idx) acc) p 0

let _statistics model =
  let open Pp in
  str" " ++ int (PMap.cardinal model.entries) ++ str" canonical universes" ++
  str", " ++ int (PMap.cardinal model.subst) ++ str" defined universes" ++
  str ", maximal value in the model is " ++ pr_opt int (model_max model) ++
  str ", minimal value is " ++ pr_opt int (model_min model) ++
  str", " ++ int (clauses_cardinal model) ++ str" clauses." ++ spc () ++
  int (without_bound model) ++ str" canonical universes are not bounded above " ++
  str", " ++ int (maximal_path model) ++ str" maximal path length in equiv nodes"

let pr_can m can =
  Level.raw_pr (Index.repr can.canon m.table)

let pr_can_clauses m ?(local=false) can =
  if not local || (local && can.local == Local) then
    if ClausesOf.is_empty can.clauses_bwd && ForwardClauses.is_empty can.clauses_fwd then Pp.mt ()
    else
      Pp.(str"For " ++ pr_can m can ++ fnl () ++ pr_clauses_of m can.canon can.clauses_bwd ++ fnl () ++
          str"Forward" ++ spc () ++ pr_fwd_clause m can.canon can.clauses_fwd ++ fnl ())
  else Pp.mt ()

let pr_clauses_all ?(local=false) m =
  let open Pp in
  PMap.fold (fun _p can acc -> pr_can_clauses ~local m can ++ acc)
    m.entries (Pp.mt ()) ++
  PMap.fold (fun p { alias_prems = u; alias_local = is_local; alias_local_eq = is_local_eq; _ } acc ->
    if not local || (local && is_local_eq == Local) then
      pr_raw_index_point m p ++ str " = " ++ pr_raw_premises m u ++ pr_local is_local ++ spc () ++ acc
    else acc)
    m.subst (Pp.mt ())

let debug_check_invariants m =
  if CDebug.get_flag debug_loop_checking_invariants_flag then
    (try check_invariants ~required_canonical:(fun _ -> false) m
     with e ->
      debug_loop_checking_invariants Pp.(fun () -> str "Broken invariants on: " ++ pr_clauses_all m ++ CErrors.print e);
      raise e)

(* PMaps are purely functional hashmaps *)

let get_canonical_value m c =
  match m.values with
  | None -> c.value
  | Some values -> PMap.find c.canon values

let canonical_value m c =
  match m.values with
  | None -> Some c.value
  | Some values -> PMap.find_opt c.canon values

let set_canonical_value m can v =
  match m.values with
  | None -> change_node m { can with value = v }
  | Some values -> { m with values = Some (PMap.add can.canon v values) }

(* let _repr_canon m can =
  let bwd = repr_clauses_of m can.clauses_bwd in
  let fwd = ForwardClauses.repr m can.clauses_fwd in
  let can = { can with clauses_bwd = bwd; clauses_fwd = fwd } in
  change_node m can, can *)

let add_opt o k =
  if Int.equal k 0 then o else Option.map ((+) k) o

let model_value m l =
  let canon =
    try repr m l
    with Not_found -> raise (Undeclared (Index.repr l m.table))
  in (canonical_value m canon)

exception VacuouslyTrue

module CanSet =
struct
  type t = ForwardClauses.t PMap.t * int (* cardinal of the PMap.t *)

  let fold f (m, _cm)  acc = PMap.fold f m acc

  let add k v (w, cw) =
    let card = ref cw in
    let upd = function
      | None -> incr card; Some v
      | Some _ -> Some v
    in
    let pm = PMap.update k upd w in
    (pm, !card)

  let mem x (w, _cw) = PMap.mem x w

  let empty = (PMap.empty, 0)

end

exception FoundImplication

let get_model_value m l k =
  (match (model_value m l) with None -> raise VacuouslyTrue | Some v -> v) - k

let min_premise (m : model) (premv : int) (prem : Premises.t option) : int =
  let g (l, k) = get_model_value m l k in
  let f prem minl = min minl (g prem) in
  match prem with
  | None -> premv
  | Some prems -> min premv (Premises.fold_ne f g prems)

let update_value premv concl m (clause : PartialClausesOf.ClauseInfo.t) : int option =
  let (conclk, premises) = clause in
  match min_premise m premv premises with
  | exception VacuouslyTrue -> None
  | k0 ->
    let newk = conclk + k0 in
    let canv = canonical_value m concl in
    debug_loop_checking Pp.(fun () -> str "Min premise value + conclk: " ++ int newk ++ str", conclusion value:: " ++ pr_opt int canv);
    match canv with
    | Some v when newk <= v -> None
    | _ -> Some newk

(** When the inference starts from the raise of a single universe [root] in a model of the other
  clauses, every update is caused by an earlier one, back to the raise of [root]. While all these
  updates are caused by single-premise clauses ([CycleRoot root]), a new raise of [root] follows a
  cycle of single-premise clauses [root + w <= root] with [w > 0], which has no model
  ([PositiveCycle]): the inference reports a loop at once, instead of going around the cycle and
  propagating the raise to the universes below it until all of them are updated. With a clause
  [concl + k <= max(p, q)], a cycle through [p] gives no loop, as [concl] can be below [q]: the
  first update by a clause with several premises gives [NoCycle]. *)
type cycle_check =
  | NoCycleCheck
  | CycleRoot of Index.t
  | NoCycle
  | PositiveCycle

(** [update_cycle cyc concl cls] is the state after an update of [concl] by one of the clauses [cls]
  from the same premise, conservatively assuming that a clause with several premises caused it *)
let update_cycle cyc concl cls =
  match cyc with
  | CycleRoot root ->
    if PartialClausesOf.exists (fun (_, prems) -> Option.has_some prems) cls then NoCycle
    else if Index.equal concl root then PositiveCycle
    else cyc
  | NoCycleCheck | NoCycle | PositiveCycle -> cyc

let check_model_clauses_of_aux m prem premv concl cls =
  PartialClausesOf.fold (fun cls m ->
    let (conclk, prems) = cls in
    debug_loop_checking Pp.(fun () -> str "Checking clause: " ++ pr_clause (pr_index_point m) (NeList.add_opt prem prems, (concl.canon,conclk)));
    match update_value premv concl m cls with
    | None -> m
    | Some newk ->
      debug_loop_checking Pp.(fun () -> str "Updating value of " ++ pr_index_point m (concl.canon,0) ++ str " to " ++ int newk);
      set_canonical_value m concl newk)
    cls m

let find_bwd idx cls = ForwardClauses.PMap.find_opt idx cls

(** Check a set of forward clauses *)
let check_model_fwd_clause_aux ?early_stop prem (fwd : ForwardClauses.t) (acc : PSet.t * model * cycle_check) =
  let open ForwardClauses in
  let check () =
    IntMap.fold (fun premk fwd (_, m, _ as acc) ->
      let premv = get_model_value m prem premk in
      PMap.fold (fun concl fwd (* (prem + premk), premises -> concl + k *) (wcls, m, cyc as acc) ->
        if cyc == PositiveCycle then acc else
        let can = repr m concl in
        let m' = check_model_clauses_of_aux m (prem, premk) premv can fwd in
        if m == m' then (* not modifed *) acc
        else (PSet.add can.canon wcls, m', update_cycle cyc can.canon fwd)) fwd acc)
      fwd acc
  in
  match early_stop with
  | None -> check ()
  | Some (can, k) ->
      let (_, m, _) = acc in
      IntMap.iter (fun premk fwd ->
        match find_bwd can.canon fwd with
        | None -> ()
        | Some cls ->
          let premv = get_model_value m prem premk in
          PartialClausesOf.iter (fun cls ->
            match update_value premv can m cls with
            | None -> ()
            | Some newk -> if k <= newk then raise FoundImplication)
            cls) fwd;
        check ()

let check_model_fwd_aux ?early_stop cyc (cls, m) : PSet.t * model * cycle_check =
  CanSet.fold (fun can fwd acc -> check_model_fwd_clause_aux ?early_stop can fwd acc) cls (PSet.empty, m, cyc)

(** The updates, see [cycle_check] *)
let check_clauses_with_premises_cycle ?early_stop cyc (cls : CanSet.t) model : (PSet.t * model * cycle_check) option =
  let (_, model', _ as res) = check_model_fwd_aux ?early_stop cyc (cls, model) in
  if model == model' then None
  else Some res

type 'a result = Loop | Model of 'a * model

let canonical_cardinal m = m.canonical

let can_all_premises_in w prem =
  Premises.for_all (fun (l, _) -> PSet.mem l w) prem

let partition_clauses_of w cls =
  PartialClausesOf.partition (fun (_k, prems) ->
    Option.cata (can_all_premises_in w) true prems) cls

let add_bwd prems kprem concl clsof =
  if PartialClausesOf.is_empty prems then clsof
  else ForwardClauses.add { prems; kprem; concl } clsof

let add_canset idx (clauses : ForwardClauses.t) canset =
  if ForwardClauses.IntMap.is_empty clauses then canset
  else CanSet.add idx clauses canset

(* Partition the clauses according to the presence of w in the premises, and only w in the conclusions *)
let partition_clauses_fwd model (w : PSet.t) (cls : CanSet.t) : CanSet.t * CanSet.t * CanSet.t =
  CanSet.fold (fun prem fwd (allw, conclw, conclnw) ->
    let fwdw, fwdpremw, fwdnw =
      ForwardClauses.fold (fun ~kprem ~concl ~prems (fwdallw, fwdnallw, fwdnw) ->
        let concl = repr model concl in
        let concl = concl.canon in
        if PSet.mem concl w then
          let allw, nallw = partition_clauses_of w prems in
          (add_bwd allw kprem concl fwdallw,
           add_bwd nallw kprem concl fwdnallw,
           fwdnw)
        else (fwdallw, fwdnallw, add_bwd prems kprem concl fwdnw))
        fwd (ForwardClauses.empty, ForwardClauses.empty, ForwardClauses.empty)
    in
    (* We do not keep bindings for all indexes *)
    let allw = add_canset prem fwdw allw (* Premises and conclusions in w *) in
    let conclw = add_canset prem fwdpremw conclw (* Conclusions in w, premises not all in w *) in
    let conclnw = add_canset prem fwdnw conclnw in (* Conclusions not in w, Premises not all in w *)
    (allw, conclw, conclnw))
    cls (CanSet.empty, CanSet.empty, CanSet.empty)

let add_fwd_clause m w cls =
  PSet.fold (fun idx cls ->
    if CanSet.mem idx cls then cls
    else
      let can = repr m idx in
      CanSet.add idx can.clauses_fwd cls)
  w cls

(* If early_stop is given, check raises FoundImplication as soon as
   it finds that the given atom is true *)

(* model is a model for the clauses outside cls.
   With [cycle], see [cycle_check], a new raise of its root answers [Loop] *)
let check_canset ?early_stop ?(cycle=NoCycleCheck) model ?(w=PSet.empty) (cls : CanSet.t) =
  let check_clauses cyc cls m = check_clauses_with_premises_cycle ?early_stop cyc cls m in
  let cV = canonical_cardinal model in
  debug_check_invariants model;
  let rec inner_loop w cardW premconclw conclw m cyc =
    (* Should consider only clauses with conclusions in w *)
    (* Partition the clauses according to the presence of w in the premises *)
    (* Warning: m is not necessarily a model for w *)
    let rec inner_loop_partition w cardW premconclw conclw m cyc =
      match loop ~inner:true cardW PSet.empty premconclw m cyc with
      | Loop -> Loop
      | Model ((wr, cyc), mr) ->
        (* This is only necessary when clauses do have multiple premises,
           otherwise each clause is either in premconclw and already considered
           or in conclw but then the premise cannot be updated and this is useless work *)
        (match check_clauses cyc conclw mr with
        | Some (_, _, PositiveCycle) -> Loop
        | Some (_wconcl, mconcl, cyc) ->
          inner_loop_partition w cardW premconclw conclw mconcl cyc
        | None -> Model ((wr, cyc), mr))
      in
      inner_loop_partition w cardW premconclw conclw m cyc
  and loop ?(inner=false) cV winit (cls : CanSet.t) m cyc =
    (* An inner loop on [w] is given all the clauses whose conclusion and premises are in [w]
       (MetaRocq's [cls ⇂ W]) and only considers them: the forward clauses of the universes it
       updates could conclude outside [w], while it reports a loop only when all the universes
       of [w] are updated *)
    let add_fwd_clause m w cls = if inner then cls else add_fwd_clause m w cls in
    match check_clauses cyc cls m with
    | None -> Model ((cls, cyc), m)
    | Some (_, _, PositiveCycle) -> Loop
    | Some (wupd, m, cyc) ->
      let w = PSet.union winit wupd in
      let cardW = PSet.cardinal w in
      if Int.equal cardW cV then Loop
      else begin
        let cls = add_fwd_clause m wupd cls in
        let (premconclw, conclw, premw) = partition_clauses_fwd m w cls in
        (match inner_loop w cardW premconclw conclw m cyc with
        | Loop -> Loop
        | Model ((wc, cyc), mc) ->
          (* wc is a subset of w *)
          (match check_clauses cyc premw mc with
          | None -> Model ((wc, cyc), mc)
          | Some (_, _, PositiveCycle) -> Loop
          | Some (w', mcls, cyc) ->
            let cls = add_fwd_clause mcls w' cls in
            loop ~inner cV (PSet.union w w') cls mcls cyc))
      end
  in
  match loop cV w cls model cycle with
  | Loop -> Loop
  | Model ((cls, _), m) -> Model (cls, m)

let check ?early_stop ?cycle model w =
  let cls = add_fwd_clause model w CanSet.empty in
  check_canset ?early_stop ?cycle model ~w cls

let expr_value m (can, k) = add_opt (canonical_value m can) (- k)

let defined_expr_value m (can, k) = get_canonical_value m can - k

let pr_model ?(local=false) model =
  Pp.(str"clauses: " ++ pr_local model.locality ++ fnl () ++ pr_clauses_all ~local model)

(** [remove_premise idx prems] removes the premise on [idx] from [prems], which are sorted and
  mention each universe once (see [sorted_premises]) *)
let remove_premise idx prems =
  let rec aux = function
    | NeList.Tip (idx', _) as l -> if Index.equal idx idx' then None else Some l
    | NeList.Cons ((idx', _) as prem, l') as l ->
      let c = Index.compare idx idx' in
      if Int.equal c 0 then Some l'
      else if c < 0 then Some l
      else match aux l' with
        | None -> Some (NeList.Tip prem)
        | Some l'' -> Some (if l'' == l' then l else NeList.Cons (prem, l''))
  in aux prems

(** [subsumed ~alive cl] holds when a clause of the conclusion of the canonical clause [cl] whose
  premises are all [alive] implies [cl]: [concl + k' <= max(P')] implies [concl + k <= max(P)]
  when each premise [u + j'] of [P'] has a premise [u + j] in [P] with [j' - k' <= j - k]. *)
let subsumed ~alive ((prems, (concl, k)) : can_clause) =
  let shift_in_prems u =
    NeList.fold (fun (can, j) acc -> if Index.equal can.canon u then Some j else acc) prems None
  in
  let implies (k', prems') =
    Premises.for_all (fun (u, j') -> alive u &&
      match shift_in_prems u with
      | Some j -> j' - k' <= j - k
      | None -> false) prems'
  in
  try ClausesOf.iter (fun cl -> if implies cl then raise_notrace Exit) concl.clauses_bwd; false
  with Exit -> true

(** [add_can_clause_model m cl] adds the clause [cl] to [m].
  @requires the premises of [cl] are sorted according to the order on their [canon]
  indices, mentioning each universe once, as produced by [simplify_can_clause]. *)
let add_can_clause_model m ((prems, (canl, conclk)) : can_clause) : (can_clause * model) option =
  let canprems = NeList.map (fun (can, k) -> (can.canon, k)) prems in
  let clof = (conclk, canprems) in
  (* Add clause to the backwards clauses of l *)
  let canl' =
    let bwd = ClausesOf.add m.locality clof canl.clauses_bwd in
    if bwd == canl.clauses_bwd then canl
    else { canl with clauses_bwd = bwd }
  in
  if canl == canl' then None else
  let m' = change_node m canl' in
  let prems', m' = (* Add clause to the forward clauses from the premises *)
    NeList.fold_map (fun ((idx0, kprem) as prem) entries ->
      let idx = if idx0 == canl then canl' else idx0 in
      let idx' =
        let fwd = ForwardClauses.add { kprem; concl = canl'.canon;
          prems = PartialClausesOf.singleton (conclk, remove_premise idx0.canon canprems) } idx.clauses_fwd in
        if fwd == idx.clauses_fwd then idx
        else { idx with clauses_fwd = fwd }
      in
      if idx0 != idx' then ((idx', kprem), change_node entries idx')
      else (prem, entries))
      prems m'
  in Some ((prems', refresh_can_expr m' (canl', conclk)), m')

let infer_clauses_extension ?cycle cans m =
  match check ?cycle m cans with
  | Loop -> None
  | Model (_updates, model) ->
    debug_check_invariants model;
    Some model

(** [in_premises idx prems] is [true] iff [idx] appears in [prems] *)
let in_premises idx prems =
  Premises.exists (fun (idx', _) -> Index.equal idx idx') prems

(** 3 Substitution in forward and backward clauses
  of a level by an expression. *)

(** [subst_fwd_clauses setidx prem idx u fwd] substitutes [idx] by [u] in the premises and conclusions of the forward clauses [fwd] of [prem].
 The clauses are simplified (see [simplify_clause]). If [prem] is [idx], the clauses become forward clauses of [u],
 otherwise the increment of [prem] changes when [u] mentions [prem], as premises on the same universe are merged.
 @param fwd A set of forward clauses of shape [prem + kprem, prems -> concl + k]. *)
let subst_fwd_clauses setidx prem idx (idx', k' as u) fwd =
  let mentions ~kprem:_ ~concl ~prems =
    Index.equal concl idx ||
    PartialClausesOf.exists (fun (_, others) -> Option.cata (in_premises idx) false others) prems
  in
  if not (Index.equal prem idx) && not (ForwardClauses.exists mentions fwd) then fwd else
  let prem' = if Index.equal prem idx then idx' else prem in
  ForwardClauses.fold
    (fun ~kprem ~concl ~prems fwd ->
      PartialClausesOf.fold (fun (kconcl, others) fwd ->
        let concl', kconcl' = if Index.equal concl idx then (idx', kconcl + k') else (concl, kconcl) in
        let prems = fwd_premises prem kprem others in
        let prems' = Premises.subst idx (NeList.Tip u) prems in
        if prems' == prems && not (Index.equal concl idx) then
          ForwardClauses.add { kprem; concl; prems = PartialClausesOf.singleton (kconcl, others) } fwd
        else match simplify_clause setidx (prems', (concl', kconcl')) with
        | Trivial -> fwd
        | Contradictory -> assert false (* The substituted equality holds in the model *)
        | Canonical (prems', _) ->
          match NeList.find (fun p -> Index.equal p prem') prems' with
          | exception Not_found -> fwd (* [prem'] is dropped from the premises when it is the conclusion *)
          | kprem ->
            let others = remove_premise prem' prems' in
            ForwardClauses.add { kprem; concl = concl'; prems = PartialClausesOf.singleton (kconcl', others) } fwd)
        prems fwd)
    fwd ForwardClauses.empty

(** [subst_bwd_clauses setidx concl idx u bwd] substitute [idx] by [u] in the premises of the backward clauses [bwd] of [concl].
  The clauses are simplified (see [simplify_clause]).
  @param bwd A set of backward clauses of shape [prems -> concl + k]
  @return A set of backward clauses of shape [prems[idx/u] -> concl + k] *)
let subst_bwd_clause setidx concl idx u (kconcl, prems as cli) =
  let prems' = Premises.subst idx (NeList.Tip u) prems in
  match simplify_clause setidx (prems', (concl, kconcl)) with
  | Trivial -> None
  | Contradictory -> assert false (* The substituted equality holds in the model *)
  | Canonical (prems', _) -> if prems' == prems then Some cli else Some (kconcl, prems')

let subst_bwd_clauses setidx concl idx u bwd  =
  ClausesOf.filter_map (fun _local -> subst_bwd_clause setidx concl idx u) bwd

(** [subst_bwd_clause_of setidx concl idx u cl bwd] substitutes [idx] by [u] in the backward
  clause [cl] of [concl], if it is in [bwd], as [subst_bwd_clauses] does *)
let subst_bwd_clause_of setidx concl idx u cl bwd =
  ClausesOf.replace cl (subst_bwd_clause setidx concl idx u) bwd

(** [subst_fwd_clause_of setidx prem idx u (kprem, concl, cl) fwd] substitutes [idx] by [u] in the
  forward clause [prem + kprem, cl -> concl] of [prem], if it is in [fwd], as [subst_fwd_clauses] does *)
let subst_fwd_clause_of setidx prem idx u (kprem, concl, cl) fwd =
  if not (ForwardClauses.mem ~kprem concl cl fwd) then fwd else
  let fwdcl = ForwardClauses.singleton { kprem; concl; prems = PartialClausesOf.singleton cl } in
  let fwdcl' = subst_fwd_clauses setidx prem idx u fwdcl in
  if fwdcl' == fwdcl then fwd
  else ForwardClauses.add_all fwdcl' (ForwardClauses.remove ~kprem concl cl fwd)

(** [clauses_mentioning other] are the clauses of the nodes other than [other] which mention [other],
  read off the clauses of [other], where they are all registered:
  - the backward clauses [(concl, (kconcl, prems))] of a clause [other + k, others -> concl + kconcl]
  - the forward clauses [(prem, (kprem, concl, (kconcl, others)))] of each premise [prem + kprem] of a
    clause [prems -> other + kconcl] or [other + k, others -> concl + kconcl] *)
let clauses_mentioning other =
  let idx = other.canon in
  let fwd_of prems concl kconcl acc =
    Premises.fold (fun (prem, kprem) acc ->
        if Index.equal prem idx then acc
        else (prem, (kprem, concl, (kconcl, remove_premise prem prems))) :: acc)
      prems acc
  in
  let fwds = ClausesOf.fold (fun _local (kconcl, prems) acc -> fwd_of prems idx kconcl acc)
      other.clauses_bwd []
  in
  ForwardClauses.fold (fun ~kprem ~concl ~prems (bwds, fwds) ->
      PartialClausesOf.fold (fun (kconcl, others) (bwds, fwds) ->
          let prems = fwd_premises idx kprem others in
          let bwds = if Index.equal concl idx then bwds else (concl, (kconcl, prems)) :: bwds in
          (bwds, fwd_of prems concl kconcl fwds))
        prems (bwds, fwds))
    other.clauses_fwd ([], fwds)

module UnivSubst =
struct

(** [subst_fwd_clauses idx u fwd] substitutes [idx] by [u] in the premises and conclusions of the forward clauses [fwd].
 @param fwd A set of forward clauses [fwd] of shape [_, prems -> concl + k].
 @return A set of forward clauses representing [_, prems[idx/u] -> concl[idx/u] + k].
  Note that substituting in a single forward clause can produce multiple forward clauses,
  if [u] is a [max]. *)
let subst_fwd_clauses idx u fwd =
  ForwardClauses.fold
    (fun ~kprem ~concl ~prems fwd' ->
      let prems' =
        PartialClausesOf.map (fun (kconcl, prems) ->
          let prems' = Option.Smart.map (Premises.subst idx u) prems in
          kconcl, prems') prems
      in
      if Index.equal concl idx then
        NeList.fold (fun (concl, kconcl) fwd' ->
          ForwardClauses.add { kprem = kprem; concl;
            prems = PartialClausesOf.shift kconcl prems' } fwd') u fwd'
      else ForwardClauses.add { kprem; concl; prems = prems' } fwd')
      fwd ForwardClauses.empty

(** [subst_bwd_clauses idx u bwd] substitute [idx] by [u] in the premises of the backward clauses [bwd].
  @param bwd A set of backward clauses of shape [prems -> _ + k]
  @return A set of backward clauses of shape [prems[idx/u] -> _ + k] *)
let subst_bwd_clauses idx u bwd  =
  ClausesOf.map (fun _local (kconcl, prems as cli) ->
    let prems' = Premises.subst idx u prems in
    if prems' == prems then cli else (kconcl, prems')) bwd

end

let enter_equiv_expr m idx local idx' k =
  enter_equiv m idx local (NeList.Tip (idx', k))

let pr_clauses model cls =
  Pp.prlist_with_sep Pp.cut (pr_clause_idx model) cls

(** [enforce_eq_can model canu canv]

  @requires canu.value = canv.value, so no new model needs to be computed.
  @returns the chosen (can + k') universe, the new [other = level + k] binding and the new model
*)
let enforce_eq_can model (canu, ku as _u) (canv, kv as _v) : (canonical_node * int) * (Index.t * (Index.t * int)) * t =
  (* assert (expr_value model u = expr_value model v); *)
  (* assert (canu != canv); *)
  (* v := u or u := v, depending on Level.is_set (for Set), and the [rigid] flags *)
  debug_check_invariants model;
  (* let model0 = model in *)
  let direction = (* true: canv := canu + k. false: canu := canv + k. *)
    if Level.is_set (Index.repr canu.canon model.table) then
      (* Set + k = l + k' -> k' < k
        -> l = Set + (k - k') *)
      (assert (kv <= ku); true)
    else if Level.is_set (Index.repr canv.canon model.table) then
      (assert (ku <= kv); false)
    else if Int.equal ku kv then
      (* A global universe stays canonical: it is rigid, and the terms keep it (see
         [normalize_flexible]), while the local ones can be removed, e.g. when restricting a
         universe context, which would drop the equalities between their aliases. *)
      if canu.local == Global && canv.local == Local then true
      else if canv.local == Global && canu.local == Local then false
      else if canu.rigid then true
      else if canv.rigid then false
      (* This heuristic choice seems to have real performance impact in e.g. math_classes/dyadics.v *)
      else if ForwardClauses.cardinal canu.clauses_fwd <= ForwardClauses.cardinal canv.clauses_fwd then
        false
      else true
    else if ku < kv then false
    else (* canu + ku = canv + kv /\ kv < ku -> canv = canu + (ku - kv) *)
      true
  in
  let can, k, other, diff, model =
    if direction then
      (canu, ku, canv, ku - kv, enter_equiv_expr model canv.canon canv.local canu.canon (ku - kv))
    else
      (canv, kv, canu, kv - ku, enter_equiv_expr model canu.canon canu.local canv.canon (kv - ku))
  in
  (* other = can + diff *)
  let can, model =
    let cank = (can.canon, diff) in
    let model, bwd, fwd =
      let setidx = Index.find Level.set model.table in
      let idx = other.canon in
      (* The clauses of the other nodes mentioning other, including can, are all registered in the
        clauses of other: we substitute in them one at a time, before substitution, as substitution
        can remove trivial clauses. Merging other then costs in the size of its clauses, not of the
        ones of can or of the other nodes, e.g. when merging many universes into a large class.
        - prems -> other + k clauses are reindexed to become prems -> can + k clauses,
          but the forward clauses for each premise in prems still mentions the now equivalent universe.
        - other, prems -> u + k clauses are reindexed to become can, prems -> u + k clauses,
          but the backward clauses for each u still mention other. *)
      let bwds, fwds = clauses_mentioning other in
      let canbwd, model = List.fold_left (fun (canbwd, model) (concl, cl) ->
          if Index.equal concl can.canon then (subst_bwd_clause_of setidx concl idx cank cl canbwd, model)
          else
            let n = repr model concl in
            let bwd = subst_bwd_clause_of setidx concl idx cank cl n.clauses_bwd in
            (canbwd, if bwd == n.clauses_bwd then model else change_node model { n with clauses_bwd = bwd }))
          (can.clauses_bwd, model) bwds
      in
      let canfwd, model = List.fold_left (fun (canfwd, model) (prem, cl) ->
          if Index.equal prem can.canon then (subst_fwd_clause_of setidx prem idx cank cl canfwd, model)
          else
            let n = repr model prem in
            let fwd = subst_fwd_clause_of setidx prem idx cank cl n.clauses_fwd in
            (canfwd, if fwd == n.clauses_fwd then model else change_node model { n with clauses_fwd = fwd }))
          (can.clauses_fwd, model) fwds
      in
      let newbwd = ClausesOf.union canbwd
        (subst_bwd_clauses setidx can.canon idx cank (ClausesOf.shift diff other.clauses_bwd))
      in
      let newfwd = ForwardClauses.add_all (subst_fwd_clauses setidx idx idx cank other.clauses_fwd) canfwd in
      model, newbwd, newfwd
    in
    debug_loop_checking_set_can Pp.(fun () ->
      str"enforce_eq_can " ++ pr_index_point model (other.canon, 0) ++
      str" := " ++ pr_index_point model cank ++
      str" new fwd " ++ pr_clauses model (ForwardClauses.to_clauses
        (NeList.Tip (can.canon, 0)) fwd));
    let can = { can with clauses_bwd = bwd; clauses_fwd = fwd } in
    can, change_node model can
  in
  debug_check_invariants model;
  (can, k), (other.canon, (can.canon, diff)), model

let pr_can_expr m (c, n) = pr_index_point m (c.canon, n)

let refresh_can_expr_can m (can, k) =
  match canonical_repr m (can.canon, k) with
  | NeList.Tip cank -> cank
  | NeList.Cons _ -> assert false (* We are only equating level expressions here. *)

let refresh_can_premises m prems = NeList.map (refresh_can_expr_can m) prems

let enforce_eq_can m can can' equivs =
  debug_loop_checking Pp.(fun () -> str"Merging " ++ pr_can_expr m can ++ str " and " ++ pr_can_expr m can');
  let can = refresh_can_expr_can m can in
  let can' = refresh_can_expr_can m can' in
  if fst can == fst can' then (can, equivs, m)
  else let can, other, m = enforce_eq_can m can can' in
    (can, other :: equivs, m)

let make_equiv m equiv =
  match equiv with
  | can :: can' :: tl ->
    (* We are about to merge all these universes as they should be equal in the model,
      they should hence have the same values *)
    if CDebug.(get_flag debug_loop_checking_invariants_flag) then
      assert (List.for_all (fun x -> expr_value m x = expr_value m can) (can' :: tl));
    let _can, equivs, m =
      List.fold_left (fun (can, equivs, m) can' -> enforce_eq_can m can can' equivs)
        (enforce_eq_can m can can' []) tl
    in
    m, equivs
  | _ -> m, []

(* let _simplify_premises m prems concl conclk : Premises.t option =
  let prems' = canonical_premises m prems in
  shrink_premises prems' concl conclk *)

type equivalences = (Index.t * (Index.t * int)) list

type 'a check_function = t -> 'a -> 'a -> bool

let update_model_value (m : model) can k' : model =
  let v = canonical_value m can in
  let k' = max_opt v k' in
  if Option.equal Int.equal k' v then m
  else
    (debug_loop_checking Pp.(fun () -> str "Updating value of " ++ pr_index_point m (can.canon,0) ++ str " to " ++ int (Option.get k'));
    set_canonical_value m can (Option.get k'))

let update_can_premises model prem =
  let g (model, canset) (l, k) =
    match canonical_value model l with
    | Some v -> ((model, canset), v - k)
    | None -> raise VacuouslyTrue
  in
  let f prem (model, minl) =
    let model, gval = g model prem in
    (model, min minl gval)
  in
  Premises.fold_ne f (g model) prem


let update_model cyc ((prems, (can, k)) : can_clause) (m : model) : PSet.t * model * cycle_check =
  match update_can_premises (m, CanSet.empty) prems with
  | exception VacuouslyTrue -> (PSet.empty, m, cyc)
  | ((m', canset), k0) ->
    let m' = update_model_value m' can (Some (k + k0)) in
    if m' != m then
      let canset = CanSet.add can.canon can.clauses_fwd canset in
      match check_clauses_with_premises_cycle cyc canset m' with
      | Some res -> res
      | None -> (PSet.empty, m', cyc)
    else (PSet.empty, m, cyc)

let infer_clause_extension cl minit =
  debug_loop_checking Pp.(fun () -> str "infer_clause_extension " ++ pr_clause (pr_can_expr minit) cl);
  match simplify_can_clause minit cl with
  | Trivial -> debug_loop_checking Pp.(fun () -> str "clause is trivial "); Some minit
  | Contradictory -> debug_loop_checking Pp.(fun () -> str "clause is contradictory "); None
  | Canonical cl ->
    match add_can_clause_model minit cl with
    | None -> (* The clause was already present in the model *)
      Some minit
    | Some ((_, (concl, _)) as cl, m) ->
      (* [minit] is a model of the other clauses: only the conclusion of [cl] is raised *)
      match update_model (CycleRoot concl.canon) cl m with
      | _, _, PositiveCycle -> None
      | cans, m, cycle ->
      if PSet.is_empty cans then begin
        (* The clause is already true in the current model,
          but might not be in an extension, so we keep it *)
        Some m
      end else
        (* The clauses are not valid in the current model, we have to find a new one *)
        (* debug Pp.(fun () -> str"Enforcing clauses requires a new inference"); *)
        match infer_clauses_extension ~cycle cans m with
        | None ->
          debug_loop_checking Pp.(fun () -> str"infer_clause_extension found loop");
          None
        | Some m ->
          debug_loop_checking Pp.(fun () -> str"infer_clause_extension found a model");
          Some m
(* A clause premises -> concl + k might hold in the current minimal model without being valid in all
   its extensions.

   We generate a new minimal model starting from the premises with their minimal values making all clauses
   involving them active. I.e. we make the premises true but let the conclusion be inferred.
   Then we check that the conclusion holds in this new minimal model. *)

(** [premises_model model prems] is the model where only the premises [prems] have values,
  and their forward clauses, from which the consequences of [prems] are propagated: in the
  resulting model, [x] has value [v] when [x + v <= max(prems)] is derived *)
let premises_model model prems =
  let model = NeList.fold (fun prem values ->
    let x, k = refresh_can_expr model prem in
    let v = model_value values x.canon in
    update_model_value values x (Some (max k (Option.default 0 v)))) prems
    { model with values = Some PMap.empty }
  in
  let cls = NeList.fold (fun (prem, _k) cls -> CanSet.add prem.canon prem.clauses_fwd cls) prems CanSet.empty in
  model, cls

let check_one_clause model prems concl k =
  let model, cls = premises_model model prems in
  (* We have a model where only the premises are true, check if the conclusion follows.
     The premises are not updated universes: starting with them would answer [Loop] as
     soon as all the other universes are updated (as in MetaRocq's [loop_check]) *)
  match check_canset ~early_stop:(concl, k) model cls with
  | exception FoundImplication -> true
  | Loop -> false
  | Model (_updates, model') ->
    match canonical_value model' concl with
    | None -> false
    | Some value -> k <= value

(** [check_one_clause_complete model prems concl k] decides whether [concl + k <= max(prems)]
  holds in all the valuations of the universes in the natural numbers satisfying [model].
  [check_one_clause] only finds the clauses derivable from the premises, which also hold
  when the universes not bounded by the premises are infinite: e.g. from [u < max(u, v)],
  it does not find [u < v]. As in MetaRocq's [check_clause] (Deciders.v), the clause holds
  iff its negation [max(prems) < concl + k], i.e. the clauses [p + kp + 1 <= concl + k] for
  each premise [p + kp], has no model with [model]. *)
let check_one_clause_complete model prems concl k =
  let rec aux m = function
    | [] -> false (* A model of the negation *)
    | (p, kp) :: prems ->
      let cl = (NeList.tip (refresh_can_expr m (concl, k)), refresh_can_expr m (p, kp + 1)) in
      match infer_clause_extension cl m with
      | None -> true
      | Some m -> aux m prems
  in
  aux model (NeList.to_list prems)

(** [fold_above model (can, k) f acc] folds [f] over the universes above [can + k] through its
  clauses [can + c <= max(prems)]: [f ~single (q, kq + k - c)] for each premise [q + kq], where
  [single] tells if it is the only one, and then [can + k <= q + (kq + k - c)] *)
let fold_above model (can, k) f acc =
  ClausesOf.fold (fun _local (c, prems) acc ->
      let single = match prems with NeList.Tip _ -> true | NeList.Cons _ -> false in
      NeList.fold (fun (q, kq) acc -> f ~single (repr model q, kq + k - c) acc) prems acc)
    can.clauses_bwd acc

(** [fold_below model (can, k) f acc] folds [f] over the universes below [can + k] through the
  clauses [concl + kconcl <= max(can + kprem, ...)]: [f ~single (concl, kconcl - kprem + k)],
  where [single] tells if [can + kprem] is the only premise, and then
  [concl + (kconcl - kprem + k) <= can + k] *)
let fold_below model (can, k) f acc =
  ForwardClauses.fold (fun ~kprem ~concl ~prems acc ->
      PartialClausesOf.fold (fun (kconcl, others) acc ->
          f ~single:(Option.is_empty others) (repr model concl, kconcl - kprem + k) acc)
        prems acc)
    can.clauses_fwd acc

(** [reach next todo seen] adds to [seen] the universes reachable from the ones of [todo] through
  [next] ([fold_above] or [fold_below]), with the first increment found for each one *)
let rec reach next todo seen =
  match todo with
  | [] -> seen
  | x :: todo ->
    let todo, seen = next x (fun (y, _ as e) (todo, seen as acc) ->
        if PMap.mem y.canon seen then acc else (e :: todo, PMap.add y.canon e seen))
        (todo, seen)
    in
    reach next todo seen

(** [reach_all model next within start] The universes reachable from the ones of [start] through
  [next] ([fold_above] or [fold_below]), among the ones satisfying [within] *)
let reach_all model next within start =
  List.fold_left (fun seen x -> if PMap.mem (fst x).canon seen then seen else
      reach (fun x f -> next model x (fun ~single:_ y acc -> if within y then f y acc else acc))
        [x] (PMap.add (fst x).canon x seen))
    PMap.empty start

(** [entails model prems (x, kx)] decides [x + kx <= max(prems)] in all the valuations of [model] *)
let entails model prems (x, kx) =
  NeList.exists (fun (p, kp) -> p == x && kx <= kp) prems ||
  let s = NeList.fold (fun (_, kp) s -> max s (- kp)) prems (max 0 (- kx)) in
  let prems = NeList.map (fun (p, kp) -> (p, kp + s)) prems in
  check_one_clause model prems x (kx + s) || check_one_clause_complete model prems x (kx + s)

(** [entails_from model (p, kp) candidates] decides [x + kx <= p + kp] as [entails] for each
  [x + kx] of [candidates], propagating the consequences of [p + kp] once for all of them
  instead of once for each: [x + kx + s <= p + kp + s] is derived when [x] gets a value at
  least [kx + s] in the model of the premise [p + kp + s], for an [s] making all the increments
  non-negative. As this is only sound, the other candidates are decided by
  [check_one_clause_complete], as in [entails]. *)
let entails_from model (p, kp) candidates =
  let s = List.fold_left (fun s (_, kx) -> max s (- kx)) (max 0 (- kp)) candidates in
  let derived =
    let pmodel, cls = premises_model model (NeList.tip (p, kp + s)) in
    match check_canset pmodel cls with
    | Loop -> None
    | Model (_updates, m) -> Some m
  in
  fun (x, kx) ->
    (x == p && kx <= kp) ||
    (match derived with
     | Some m -> (match canonical_value m x with Some v -> kx + s <= v | None -> false)
     | None -> false) ||
    let s = max 0 (max (- kp) (- kx)) in
    check_one_clause_complete model (NeList.tip (p, kp + s)) x (kx + s)

(** [witness_models model rcan (y0, d0)] The models of [model] where [r] and [y0 + d0] are not
  equal: its extensions by the negations [r + 1 <= y0 + d0] and [y0 + d0 + 1 <= r] of the two
  halves of [r = y0 + d0] (as in [check_one_clause_complete]). There are none when they are equal
  in all the valuations of [model]. *)
let witness_models model rcan (y0, d0) =
  let y0can = repr model y0 in
  let s = max 0 (- d0) in
  List.filter_map (fun cl -> infer_clause_extension cl model)
    [ (NeList.tip (y0can, d0 + s), (rcan, 1 + s));
      (NeList.tip (rcan, s), (y0can, d0 + 1 + s)) ]

(** [same_differences model witnesses x y] Two universes equal in all the valuations of [model]
  have the same difference of values in all its models: [x] and [y] can only be equal if their
  difference in each of the models [witnesses] of [model] is the one in [model]. *)
let same_differences model witnesses x y =
  let value m idx = canonical_value m (repr m idx) in
  let d = get_canonical_value model (repr model y) - get_canonical_value model (repr model x) in
  List.for_all (fun m' ->
      match value m' y, value m' x with
      | Some vy, Some vx -> Int.equal (vy - vx) d
      | _ -> true) witnesses

(** [find_to_merge model prems (canv, kv)] For a clause [prems -> canv + kv] of [model], whose
  values make [max(prems)] and [canv + kv] equal, computes the universes [x + kx] such that
  [max(prems) <= x + kx <= canv + kv], which are all equal to [canv + kv]. The result is a list
  starting with [canv + kv], or [[]] if there is no other such universe.
  In any model, the clauses between equal universes hold with equality: they are tight, and
  the increment [kx] of each universe [x] is determined by its value.
  For a single premise [p + kp], these universes are the ones reachable from [p + kp] through
  tight clauses with a single premise from which [canv + kv] is reachable: if no clause with
  several premises is met above [p + kp], this is complete. Otherwise, and for several
  premises, the universes above and below [canv + kv] in the graph of clauses are checked to
  be equal to it in all valuations, as in [check_leq]: this is complete. *)
let find_to_merge model prems (canv, kv) =
  let value = defined_expr_value model (canv, kv) in
  let tight x = Int.equal (defined_expr_value model x) value in
  (* The universes above through the tight clauses [can + c <= q + kq], noting in [skipped]
     if a clause with several premises is met *)
  let skipped = ref false in
  let above x f =
    fold_above model x (fun ~single y acc ->
        if not single then (skipped := true; acc)
        else if tight y then f y acc else acc)
  in
  (* The universes below through the tight clauses [concl + kconcl <= can + kprem], among the
     ones satisfying [within] *)
  let below within x f = fold_below model x (fun ~single y acc -> if single && within y then f y acc else acc) in
  (* The universes [t + kt] equal to [canv + kv] in all valuations: as [model] has the clause,
     [max(prems) <= t + kt] is not required, a premise can be below [canv + kv] in all valuations.
     Such a [t] is below [canv] in the graph of clauses, following all their premises:
     otherwise, the universes above [t] could all be raised. It is also above [canv], through
     universes below [canv] as well. Its increment [kt] is [value(t) - value]. *)
  let complete () =
    (* [Set] is below every universe *)
    let setcan = repr model (Index.find Level.set model.table) in
    let below = reach_all model fold_below (fun _ -> true) [(canv, kv); (setcan, 0)] in
    let above = reach_all model fold_above (fun (y, _) -> PMap.mem y.canon below) [(canv, kv)] in
    let candidates = PMap.fold (fun idx _ acc ->
        let t = repr model idx in
        (t, get_canonical_value model t - value) :: acc)
      above []
    in
    (* [canv + kv = t + kt] iff [canv = t + (kt - kv)]. The models where [canv] and the first
       other candidate are not equal refute at once the equality of the candidates whose difference
       with [canv] they change, see [batch_classes]. *)
    let candidates =
      match List.find_opt (fun (t, _) -> t != canv) candidates with
      | None -> candidates
      | Some (t0, kt0) ->
        let witnesses = witness_models model canv (t0.canon, kt0 - kv) in
        List.filter (fun (t, _) -> same_differences model witnesses canv.canon t.canon) candidates
    in
    let below_canv = entails_from model (canv, kv) candidates in
    List.filter (fun (t, kt) -> below_canv (t, kt) && entails model (NeList.tip (t, kt)) (canv, kv))
      candidates
  in
  let members = match prems with
    | NeList.Tip (p, _ as pk) ->
      if not (tight pk) then [] else
      let f = reach above [pk] (PMap.singleton p.canon pk) in
      if !skipped then complete ()
      else if not (PMap.mem canv.canon f) then []
      else
        (* The increment found going down must be the one of [x] in [f]: the clause is tight *)
        let within (x, k) =
          match PMap.find_opt x.canon f with
          | Some (_, k') -> Int.equal k k'
          | None -> false
        in
        let d = reach (below within) [(canv, kv)] (PMap.singleton canv.canon (canv, kv)) in
        PMap.fold (fun _ x acc -> x :: acc) d []
    | NeList.Cons _ -> complete ()
  in
  match List.filter (fun (can, _) -> not (Index.equal can.canon canv.canon)) members with
  | [] -> []
  | members -> (canv, kv) :: members

(** [sccs nodes succ] The strongly connected components with several elements of the graph on
  the indices of [nodes], whose edges from [v] are given by [succ v f], calling [f] on each
  successor in [nodes] (Tarjan's algorithm) *)
let sccs nodes succ =
  let index = ref PMap.empty and low = ref PMap.empty and onstack = ref Index.Set.empty in
  let stack = ref [] and counter = ref 0 and result = ref [] in
  let lower v k = if k < PMap.find v !low then low := PMap.add v k !low in
  let rec visit v =
    index := PMap.add v !counter !index;
    low := PMap.add v !counter !low;
    incr counter;
    stack := v :: !stack;
    onstack := Index.Set.add v !onstack;
    succ v (fun w ->
        if not (PMap.mem w !index) then (visit w; lower v (PMap.find w !low))
        else if Index.Set.mem w !onstack then lower v (PMap.find w !index));
    if Int.equal (PMap.find v !low) (PMap.find v !index) then
      let rec pop acc = match !stack with
        | [] -> assert false
        | w :: rest ->
          stack := rest;
          onstack := Index.Set.remove w !onstack;
          if Index.equal w v then w :: acc else pop (w :: acc)
      in
      match pop [] with [_] -> () | scc -> result := scc :: !result
  in
  PMap.iter (fun v _ -> if not (PMap.mem v !index) then visit v) nodes;
  !result

(** [batch_classes model cls] For clauses [cls] of [model], computes the classes of equal
  universes that they can create, all at once, as [find_to_merge] and [zone_classes] do for a
  single clause. The universes made equal are in the zone of the universes below a conclusion
  of [cls] or [Set], and above one of their premises, in the graph of clauses following all
  their premises: two universes of the zone are candidates if they are in the same strongly
  connected component, through the clauses and the implicit clauses [Set <= x]. The universes
  in a cycle of tight clauses with a single premise are equal, as in [find_to_merge]; the other
  candidates are checked to be equal in all valuations, as in [zone_classes]. The candidates of a
  component are grouped with the first one [r] of them, then with the first one of the remaining
  ones, and so on: the models of [witness_models] where [r] and a candidate are not equal refute
  at once the equality of all the universes whose differences of values they change, for the
  following groups too, so that most of the candidates are not checked by [entails]. *)
let batch_classes model cls =
  let setcan = repr model (Index.find Level.set model.table) in
  let setidx = setcan.canon in
  let concls = List.map (fun (_, concl) -> refresh_can_expr_can model concl) cls in
  let prems = List.concat_map (fun (prems, _) -> NeList.to_list (refresh_can_premises model prems)) cls in
  let below = reach_all model fold_below (fun _ -> true) ((setcan, 0) :: concls) in
  let zone = reach_all model fold_above (fun (y, _) -> PMap.mem y.canon below) prems in
  let zone = PMap.filter (fun idx _ -> PMap.mem idx below) zone in
  if PMap.cardinal zone <= 1 then [] else
  let value idx = get_canonical_value model (repr model idx) in
  let succ_all v f =
    if Index.equal v setidx then PMap.iter (fun w _ -> f w) zone
    else fold_above model (repr model v, 0)
        (fun ~single:_ (q, _) () -> if PMap.mem q.canon zone then f q.canon) ()
  in
  (* The tight clauses [x <= q + kq] with a single premise, and [Set <= x] *)
  let succ_tight v f =
    let x = repr model v in
    let vx = get_canonical_value model x in
    fold_above model (x, 0) (fun ~single (q, _ as qk) () ->
        if single && PMap.mem q.canon zone && Int.equal (defined_expr_value model qk) vx
        then f q.canon) ();
    if Index.equal v setidx then PMap.iter (fun w _ -> if Int.equal (value w) vx then f w) zone
  in
  (* Each universe of a cycle of tight clauses is mapped to the first one of its cycle *)
  let unit_of = List.fold_left (fun m scc ->
      let r = List.hd scc in List.fold_left (fun m x -> PMap.add x r m) m scc)
      PMap.empty (sccs zone succ_tight)
  in
  let unit x = Option.default x (PMap.find_opt x unit_of) in
  let candidates = sccs zone succ_all in
  List.fold_left (fun classes scc ->
      (* The members of each cycle of tight clauses, in the order of [scc] *)
      let order, members = List.fold_left (fun (order, members) x ->
          let u = unit x in
          match PMap.find_opt u members with
          | Some xs -> (order, PMap.add u (x :: xs) members)
          | None -> (u :: order, PMap.add u [x] members)) ([], PMap.empty) scc
      in
      let units = List.rev_map (fun u -> (u, PMap.find u members)) order in
      (* [witnesses] are models of [model], kept from one group to the next *)
      let rec group witnesses units classes = match units with
        | [] -> classes
        | (r, rs) :: units ->
          let vr = value r in
          let rcan = repr model r in
          let eq, units, witnesses =
            match List.find_opt (fun (y, _) -> same_differences model witnesses r y) units with
            | None -> [], units, witnesses
            | Some (y0, _) ->
              let witnesses = witness_models model rcan (y0, value y0 - vr) @ witnesses in
              let candidate (y, _) = same_differences model witnesses r y in
              let below_r =
                entails_from model (rcan, 0)
                  (List.filter_map (fun (y, _ as u) ->
                       if candidate u then Some (repr model y, value y - vr) else None) units)
              in
              let eq, units = List.partition (fun (y, _ as u) ->
                  let ky = value y - vr in
                  let ycan = repr model y in
                  candidate u &&
                  below_r (ycan, ky) && entails model (NeList.tip (ycan, ky)) (rcan, 0))
                  units
              in
              eq, units, witnesses
          in
          let members = rs @ List.concat_map snd eq in
          let cls = List.map (fun x -> (repr model x, value x - vr)) members in
          group witnesses units (match cls with [] | [_] -> classes | _ -> cls :: classes)
      in
      group [] units classes)
    [] candidates

(** [zone_classes model prems (canv, kv)] For a clause [prems -> canv + kv] of [model], computes
  the classes of equal universes, other than the class of [canv + kv], that the clause can create.
  They are not necessarily between [canv] and a premise: the clause can make a premise of another
  clause [c <= max(q, ...)] useless (always below [c]), e.g. [canv] itself, creating equalities
  through the remaining premises. They are looked for in the zone of the universes below [canv]
  or [Set], and above a premise, in the graph of clauses following all their premises. Two
  universes of the zone are candidates if they are in the same strongly connected component,
  through the clauses and the implicit clauses [Set <= x], and are then checked to be equal in
  all valuations, as in [check_leq]. This is checked by [-d loop-checking-merged]. *)
(* The strongly connected components of the zone are those of [batch_classes] for the single clause,
   computed in linear time. *)
let zone_classes model prems (canv, _ as v) =
  let setcan = repr model (Index.find Level.set model.table) in
  if ForwardClauses.is_empty setcan.clauses_fwd &&
     not (ForwardClauses.exists (fun ~kprem:_ ~concl ~prems:_ ->
         not (Index.equal concl setcan.canon)) canv.clauses_fwd)
  then [] else
  if (match prems with NeList.Tip (p, _) -> ClausesOf.is_empty p.clauses_bwd | NeList.Cons _ -> false)
  then [] else
  batch_classes model [(prems, v)]

(** [simplify_clauses_between model u v] Checks if [v <= u] holds, in which case it
  merges the equivalence classes of universes between [u] and [v]. If [v] is the lub
  of [v1..vn], they might not be merged while other universes between [u] and [v] are merged.
    @param model Assumes [u <= v] holds already
    @return a potentially modified model, without changing any values *)
let simplify_clauses_between model u prems : t * equivalences =
  (* Values are inverted: the value of [max(prems)] is the least value of the premises *)
  let premsmax = (Premises.fold (fun u m -> min_opt (expr_value model u) m) prems None) in
  let model, equivs =
    if not (Option.equal Int.equal premsmax (expr_value model u)) then
      (* We know v -> u and check for u -> v, this can only be true if both expressions
        already have the same value *)
      model, []
    else
      make_equiv model (find_to_merge model prems u)
  in
  (* [make_equiv] may have merged [u] or the premises: their nodes are no longer canonical *)
  let u = refresh_can_expr_can model u in
  let prems = refresh_can_premises model prems in
  List.fold_left (fun (model, equivs) cls ->
      let model, equivs' = make_equiv model cls in model, equivs' @ equivs)
    (model, equivs) (zone_classes model prems u)

let canonical_repr_level_expr m (u, k) : can_premises =
  try canonical_repr m (Index.find u m.table, k)
  with Not_found ->
    CErrors.anomaly ~label:"Univ.repr"
      Pp.(str"Universe " ++ Level.raw_pr u ++ str" undefined" ++
      (if Index.mem u m.table then str" (index found)" else str " (index not found in " ++ Level.Set.pr Level.raw_pr (Index.dom m.table) ++ str")") ++ str".")

let level_expr_premises m (u, k) : Premises.t =
  try NeList.Tip (Index.find u m.table, k)
  with Not_found ->
    CErrors.anomaly ~label:"Univ.repr"
      Pp.(str"Universe " ++ Level.raw_pr u ++ str" undefined" ++
      (if Index.mem u m.table then str" (index found)" else str " (index not found in " ++ Level.Set.pr Level.raw_pr (Index.dom m.table) ++ str")") ++ str".")

let unrepr_equivalences model (idxs : equivalences) =
  List.map (fun (idx, (idx', k)) -> (Index.repr idx model.table, (Index.repr idx' model.table, k))) idxs

let premises_of_universe m u =
  let ur = Universe.repr u in
  let prems = NeList.of_list ur in
  NeList.concat_map (level_expr_premises m) prems

let decompose_eq_constraints u k v =
  match k with
  | UnivConstraint.Le -> [(u, v)]
  | UnivConstraint.Eq -> [(u, v); (v, u)]

(** [enforce_clauses cls m] enforces the clauses [concl + k <= max(prems)] of [cls], given as
  pairs [(prems, (concl, k))] of universes which need not be canonical, all at once: the clauses
  are added to the model and the values of their conclusions raised, then a model is inferred
  from the raised universes, and only then are the equalities created by each clause found and
  merged, as in [simplify_clauses_between].
  @return [None] if the clauses are inconsistent with [m] *)
(** Batches of at most this many clauses are merged one clause at a time *)
let batch_threshold = 16

let enforce_clauses ?(entailed=false) cls m =
  (* Adding a clause or raising a value changes nodes: they are looked up again for each clause,
     given by the canonical universes, which do not change until the merges *)
  let add_can_clause (prems, concl) acc =
    match acc with
    | None -> None
    | Some (m, added, raised) ->
      match simplify_can_clause m (canonical_premises_repr m prems, repr_expr m concl) with
      | Trivial -> acc
      | Contradictory -> None
      | Canonical (NeList.Cons _, _ as cl) when subsumed ~alive:(fun _ -> true) cl ->
        (* A clause with several premises implied by a clause of its conclusion, e.g.
           [u <= max(v, w)] once [u <= v] holds: it creates no equality and raises no value, and
           would only make the graph of clauses following all their premises larger *)
        acc
      | Canonical cl ->
        match add_can_clause_model m cl with
        | None -> acc (* The clause was already present in the model *)
        | Some ((prems, (can, k)) as cl, m) ->
          (* The value of the conclusion is raised, but not propagated yet *)
          match update_can_premises (m, CanSet.empty) prems with
          | exception VacuouslyTrue -> assert false (* The declared universes have values *)
          | (_, k0) ->
            let m' = update_model_value m can (Some (k + k0)) in
            Some (m', cl :: added, if m' == m then raised else PSet.add can.canon raised)
  in
  (* A conclusion substituted by [max(a, b)] gives a clause for each of [a] and [b] *)
  let add_clause acc (prems, concl) =
    match acc with
    | None -> None
    | Some (m, _, _) ->
      let concls = canonical_can_premises (canonical_repr m concl) in
      NeList.fold (fun concl acc -> add_can_clause (prems, concl) acc) concls acc
  in
  match List.fold_left add_clause (Some (m, [], PSet.empty)) cls with
  | None -> None
  | Some (m, _, raised) when entailed && PSet.is_empty raised ->
    (* The clauses were entailed by the model: they create no equality *)
    Some (m, [])
  | Some (m, added, raised) ->
    let m =
      if PSet.is_empty raised then Some m else
      (* [m] is a model of the clauses whose conclusion is not raised: from a single raised
         universe, a positive cycle of single-premise clauses through it is found at once *)
      let cycle =
        if Int.equal (PSet.cardinal raised) 1 then CycleRoot (PSet.choose raised) else NoCycleCheck
      in
      match check_clauses_with_premises_cycle cycle (add_fwd_clause m raised CanSet.empty) m with
      | None -> Some m
      | Some (_, _, PositiveCycle) -> None
      | Some (modified, m, cycle) -> infer_clauses_extension ~cycle modified m
    in
    let merge (m, equivs) (prems, concl) =
      let concl = refresh_can_expr_can m concl in
      let prems = refresh_can_premises m prems in
      match simplify_can_clause m (prems, concl) with
      | Trivial -> (m, equivs)
      | Contradictory -> assert false (* The clause holds in [m] *)
      | Canonical (prems, concl) ->
        let m, equivs' = simplify_clauses_between m concl prems in
        (m, equivs' @ equivs)
    in
    (* For a few clauses, the equalities are searched from each one, as when they are enforced
       one at a time: the universes made equal by the last clause of a cycle are merged into its
       conclusion. [find_to_merge] and [zone_classes] mostly stop early, while the zone of the whole
       batch is computed. *)
    if List.length added <= batch_threshold then
      Option.map (fun m -> List.fold_left merge (m, []) added) m
    else
      (* Searching the equalities created by each clause would explore the universes around
         them once per clause, e.g. for the many clauses of a library: they are found all at once *)
      Option.map (fun m ->
          List.fold_left (fun (m, equivs) cls ->
              let m, equivs' = make_equiv m cls in m, equivs' @ equivs)
            (m, []) (batch_classes m added)) m

(** The clauses [l + k <= max(prems v)] for each [l + k] of [u], and the converse ones for [Eq] *)
let clauses_of_constraint m (u, k, v) =
  let pu = premises_of_universe m u in
  let pv = premises_of_universe m v in
  List.concat_map (fun (u, v) -> List.map (fun u -> (v, u)) (NeList.to_list u))
    (decompose_eq_constraints pu k pv)

(* The queries of the checks of [-d loop-checking-merged] would check the invariants of the whole
   model each time *)
let without_invariant_checks f =
  let inv = CDebug.get_flag debug_loop_checking_invariants_flag in
  CDebug.set_flag debug_loop_checking_invariants_flag false;
  Fun.protect ~finally:(fun () -> CDebug.set_flag debug_loop_checking_invariants_flag inv) f

(** With [-d loop-checking-merged], [check_merged model u v] checks that the canonical universes
  near the ones of [u] and [v], at most two clauses away in both directions, and [Set], are not
  equal in all valuations: the equalities created by enforcing a constraint between [u] and [v]
  have been merged. This is checked exactly, independently of [find_to_merge] and [zone_classes],
  for at most 16 universes. *)
let check_merged model u v =
  let max_near = 16 in
  let setcan = repr model (Index.find Level.set model.table) in
  let start = List.concat_map (fun u ->
      Level.Set.fold (fun l acc -> NeList.to_list (canonical_repr_level_expr model (l, 0)) @ acc)
        (Universe.levels u) []) [u; v]
  in
  let add near (x, _) = if PMap.cardinal near >= max_near then near else PMap.add x.canon x near in
  let near = List.fold_left add (PMap.singleton setcan.canon setcan) start in
  let rec visit d near xs =
    if d = 0 then near else
    let near, next = List.fold_left (fun acc x ->
        let f ~single:_ (y, _ as e) (near, next as acc) =
          if PMap.mem y.canon near || PMap.cardinal near >= max_near then acc
          else (add near e, e :: next)
        in
        fold_below model x f (fold_above model x f acc)) (near, []) xs
    in
    visit (d - 1) near next
  in
  let near = PMap.bindings (visit 2 near start) in
  List.iter (fun (idx, x) ->
      List.iter (fun (idy, y) ->
          if Index.compare idx idy < 0 then
            let ky = get_canonical_value model y - get_canonical_value model x in
            if entails model (NeList.tip (x, 0)) (y, ky) && entails model (NeList.tip (y, ky)) (x, 0) then
              CErrors.anomaly Pp.(str "Loop_checking: the universes " ++ pr_can_expr model (x, 0) ++
                                  str " and " ++ pr_can_expr model (y, ky) ++ str " are equal but not merged."))
        near)
    near

(** [enforce_constraints csts m] enforces the constraints [csts] all at once, see [enforce_clauses] *)
let enforce_constraints csts m =
  let res = enforce_clauses (List.concat_map (clauses_of_constraint m) csts) m in
  if CDebug.get_flag debug_loop_checking_merged_flag then
    without_invariant_checks (fun () ->
        Option.iter (fun (m, _) -> List.iter (fun (u, _, v) -> check_merged m u v) csts) res);
  Option.map (fun (m, equivs) -> m, unrepr_equivalences m equivs) res

let enforce u k v m = enforce_constraints [(u, k, v)] m

let localize csts m =
  let localize_clause m (prems, concl) =
    let concls = canonical_can_premises (canonical_repr m concl) in
    NeList.fold (fun concl m ->
        match simplify_can_clause m (canonical_premises_repr m prems, repr_expr m concl) with
        | Trivial | Contradictory -> m
        | Canonical (prems, (can, k)) ->
          let clof = (k, NeList.map (fun (p, kp) -> (p.canon, kp)) prems) in
          match ClausesOf.localize clof can.clauses_bwd with
          | None -> m
          | Some clauses_bwd -> change_node m { can with clauses_bwd })
      concls m
  in
  List.fold_left localize_clause m (List.concat_map (clauses_of_constraint m) csts)

let enforce_eq u v m = enforce u UnivConstraint.Eq v m
let enforce_leq u v m = enforce u UnivConstraint.Le v m
let enforce_lt u v m = enforce_leq (Universe.addn u 1) v m

(** [unbounded_above model prems concl] holds when no premise of [prems], nor [Set], is above
  [concl] in the graph of clauses following all their premises, among at most [max_above]
  universes. Then [concl + k <= max(prems)] is not entailed: raising the universes above [concl],
  [concl] included, by the same large amount gives a model of the clauses (the clauses of these
  universes only mention universes above them, the other clauses get greater premises) where
  [concl + k] is above [max(prems)]. This refutes at once the clauses whose premises have a large
  graph below them, e.g. global universes of the Corelib, where [check_one_clause] and
  [check_one_clause_complete] would explore all of it. *)
let max_above = 1024

let unbounded_above model prems concl =
  let setidx = Index.find Level.set model.table in
  let target idx = Index.equal idx setidx || NeList.exists (fun (p, _) -> Index.equal p.canon idx) prems in
  let exception Unknown in
  let rec aux todo seen n =
    match todo with
    | [] -> true
    | x :: todo ->
      let todo, seen, n = ClausesOf.fold (fun _local (_, qs) acc ->
          NeList.fold (fun (q, _) (todo, seen, n as acc) ->
              if Index.Set.mem q seen then acc
              else if target q || n >= max_above then raise_notrace Unknown
              else (q :: todo, Index.Set.add q seen, n + 1)) qs acc)
          (repr model x).clauses_bwd (todo, seen, n)
      in
      aux todo seen n
  in
  not (target concl.canon) &&
  try aux [concl.canon] (Index.Set.singleton concl.canon) 0 with Unknown -> false

let check_leq_can canu canv model =
  match simplify_can_clause model (canv, canu) with
  | Trivial -> true
  | Contradictory -> false
  | Canonical (prems, (concl, k)) ->
    not (unbounded_above model prems concl) &&
    (check_one_clause model prems concl k || check_one_clause_complete model prems concl k)

let rec check_leq_premises m (u, v) =
  let canv = canonical_premises_repr m v in
  NeList.fold (fun (u, k) res ->
    if res then
      let canu = canonical_repr m (u, k) in
      match canu with
      | NeList.Tip canu -> check_leq_can canu canv m
      | _ -> check_leq_premises m (canonical_can_premises canu, v)
    else res) u true

let check_constraint (m : t) u k u' =
  let pu = premises_of_universe m u in
  let pu' = premises_of_universe m u' in
  let cls = decompose_eq_constraints pu k pu' in
  List.fold_left (fun check cl -> check && check_leq_premises m cl) true cls

let check_leq m u v = check_constraint m u UnivConstraint.Le v
let check_eq m u v =
  match Universe.repr u, Universe.repr v with
  | [ur], [vr] ->
    begin match canonical_repr_level_expr m ur, canonical_repr_level_expr m vr with
    | NeList.Tip cu, NeList.Tip cv ->
      (* Universes equal in all valuations are merged, which [-d loop-checking-merged] checks *)
      let res = eq_can_expr cu cv in
      if CDebug.get_flag debug_loop_checking_merged_flag
         && not (Bool.equal res (without_invariant_checks (fun () -> check_constraint m u UnivConstraint.Eq v)))
      then begin
        let pu = Universe.raw_pr u and pv = Universe.raw_pr v in
        CErrors.anomaly Pp.(str "Loop_checking: check_eq " ++ pu ++ str " " ++ pv ++
                            str " is " ++ bool res ++ str " but the constraint does not agree.")
      end;
      res
    | cu, cv ->
      (* A level substituted by [max(a, b)] is equal to [b] once [a <= b] holds, without being merged *)
      NeList.equal eq_can_expr cu cv || check_constraint m u UnivConstraint.Eq v
    end
  | _, _ -> check_constraint m u UnivConstraint.Eq v

let enforce_constraint (u, k, v) (m : t) = enforce u k v m

exception AlreadyDeclared

let add_model ?(rigid=false) u { locality; entries; subst; subst_deps; table; values; canonical; locals; local_eqs } =
  let idx, table =
    if Index.mem u table then
      let idx = Index.find u table in
      if PMap.mem idx entries || PMap.mem idx subst then raise AlreadyDeclared
      else (* Allow reuse *) idx, table
    else Index.fresh u table
  in
  let can = { canon = idx; value = 0; local = locality; rigid;
    clauses_fwd = ForwardClauses.empty; clauses_bwd = ClausesOf.empty } in
  let entries = PMap.add idx can entries in
  let locals = match locality with Local -> Index.Set.add idx locals | Global -> locals in
  idx, { locality; entries; subst; subst_deps; table; values; canonical = canonical + 1; locals; local_eqs }

let add ?rigid u model =
  let _idx, model = add_model ?rigid u model in
  model

let check_declared model us =
  let check l = not (Index.mem l model.table) in
  let undeclared = Level.Set.filter check us in
  if Level.Set.is_empty undeclared then Ok ()
  else Error undeclared

let is_declared model l = Index.mem l model.table

(** {2 Explanations of inconsistencies}

  When [enforce_constraint cst model] fails, the clauses of [cst], with the ones of [model], have
  no model. [get_explanation] shows a chain of inequalities [r < ... <= l] when a clause
  [l <= r] of [cst] is refuted by a path of clauses with a single premise. Otherwise, as with
  clauses [u <= max(l, k)], the inconsistency is not a path but a loop: it gives a minimal set
  of constraints of [model] inconsistent with [cst].

  These clauses are among the ones between the premises and conclusions of the clauses of
  [cst], i.e. the clauses whose conclusion and premises are all above the premises and below
  the conclusions: a clause outside does not depend on the conclusions or does not entail the
  premises, and the clauses of [model] alone are consistent. Every universe is above [Set]. *)

type extended_constraint_type =
  | ULe | ULt | UEq

type explanation =
  | Chain of Universe.t * (extended_constraint_type * Universe.t) list
  | Constraints of (Universe.t * extended_constraint_type * Universe.t) list

(** An explained clause [concl <= max(prems)] of the constraint [orig_prems <= orig_concl + _] *)
type explained_clause = {
  orig_prems : Universe.t;
  orig_concl : Level.t * int;
  clause : can_clause;
}

(** [explained_clauses model cst] are the clauses of the constraint [cst], in canonical form *)
let explained_clauses model (u, k, v) =
  let leq (u, v) =
    let canv = canonical_premises_repr model (premises_of_universe model v) in
    let rec clauses orig_concl u acc =
      NeList.fold (fun e acc ->
          match canonical_repr model e with
          | NeList.Tip canu ->
            (match simplify_can_clause model (canv, canu) with
             | Trivial -> acc
             | Contradictory -> { orig_prems = v; orig_concl; clause = (canv, canu) } :: acc
             | Canonical clause -> { orig_prems = v; orig_concl; clause } :: acc)
          | canu -> clauses orig_concl (canonical_can_premises canu) acc)
        u acc
    in
    List.fold_left (fun acc e -> clauses e (level_expr_premises model e) acc) [] (Universe.repr u)
  in
  let dirs = match k with UnivConstraint.Le -> [(u, v)] | UnivConstraint.Eq -> [(u, v); (v, u)] in
  List.concat_map (fun d -> List.rev (leq d)) dirs

(** [paths_above model start] maps the universes [x] above [start = r + kr] through the clauses
  with a single premise to the least [kx] such that [r + kr <= x + kx] is derived this way, and
  the universe [x] is reached from *)
let paths_above model start =
  let setidx = Index.find Level.set model.table in
  let rec aux todo best =
    match todo with
    | [] -> best
    | (x, kx as e) :: todo ->
      if fst (fst (PMap.find x.canon best)) < kx then aux todo best (* Superseded *)
      else
        let improve (y, ky) (todo, best as acc) =
          match PMap.find_opt y.canon best with
          | Some ((ky', _), _) when ky' <= ky -> acc
          | _ -> ((y, ky) :: todo, PMap.add y.canon ((ky, y), Some x.canon) best)
        in
        let acc = fold_above model e (fun ~single y acc -> if single then improve y acc else acc) (todo, best) in
        let todo, best =
          if Index.equal x.canon setidx then
            PMap.fold (fun _ y acc -> improve (y, kx) acc) model.entries acc
          else acc
        in
        aux todo best
  in
  let (r, kr) = start in
  aux [start] (PMap.singleton r.canon ((kr, r), None))

(** [chain_of_path model start path] shows the derivation [x0 + k0 <= x1 + k1 <= ...] of
  [start = x0 + k0] and [path = [x1, k1; ...]] as a chain of inequalities with non-negative
  increments. From [x + e], a step [x + kx <= y + ky] is shown as [x + e <= y + (e + ky - kx)],
  or with [<] and [y] when [e + ky - kx < 0]. *)
let chain_of_path model (x0, k0) path =
  let univ x k = Universe.of_expr (expr_of_can_premise model (x, k)) in
  let rec aux (x, kx) e = function
    | [] -> [], e
    | (y, ky as next) :: path ->
      let need = e + ky - kx in
      let steps, e' =
        if need >= 0 then [ULe, univ y need], need
        else if need = -1 then [ULt, univ y 0], 0
        else [(ULt, univ x (e - need - 1)); (ULt, univ y 0)], 0
      in
      let chain, e = aux next e' path in
      steps @ chain, e
  in
  aux (x0, k0) k0 path

(** [explain_chain model paths cl] is a chain refuting the explained clause [cl] when its
  premise is a single universe [r + kr] and it is refuted by a path of clauses with a single
  premise: [r + kr <= l + kx] with [kx < kl], its conclusion being [l + kl]. [paths] computes
  the [paths_above] a universe *)
let explain_chain model paths { orig_prems; orig_concl = (w, kw); clause } =
  match clause with
  | NeList.Cons _, _ -> None
  | NeList.Tip start, (l, kl) ->
    let best = paths start in
    match PMap.find_opt l.canon best with
    | Some ((kx, _), _) when kx < kl ->
      let rec path idx acc =
        match PMap.find idx best with
        | (_, None) -> acc
        | ((k, x), Some pred) -> path pred ((x, k) :: acc)
      in
      let chain, e = chain_of_path model start (path l.canon []) in
      let start_univ = Universe.of_expr (expr_of_can_premise model start) in
      let chain = if Universe.equal orig_prems start_univ then chain else (UEq, start_univ) :: chain in
      (* [w + kw] is [l + kl], so [l + e] is [w + (e - (kl - kw))] *)
      let chain =
        if Level.equal w (Index.repr l.canon model.table) || e - (kl - kw) < 0 then chain
        else chain @ [UEq, Universe.of_expr (w, e - (kl - kw))]
      in
      (* A contradictory clause [r + kl <= r + kr] *)
      let chain = if CList.is_empty chain then [ULt, Universe.of_expr (expr_of_can_premise model (l, kl))] else chain in
      Some (Chain (orig_prems, chain))
    | _ -> None

(** The constraint [concl + k <= max(prems)] of a clause *)
let constraint_of_can_clause model ((prems, concl) : can_clause) : UnivConstraint.t =
  (Universe.of_list [expr_of_can_premise model concl], UnivConstraint.Le, univ_of_can_premises model prems)

(** The clause [concl + k <= max(prems)], with non-negative increments, using [<] when [k > 0] *)
let explain_can_clause model ((prems, (concl, k)) : can_clause) =
  let s = NeList.fold (fun (_, kp) s -> max s (- kp)) prems (max 0 (- k)) in
  let prems = univ_of_can_premises model (NeList.map (fun (p, kp) -> (p, kp + s)) prems) in
  let k = k + s in
  let univ k = Universe.of_expr (expr_of_can_premise model (concl, k)) in
  if k > 0 then (univ (k - 1), ULt, prems) else (univ k, ULe, prems)

let enforce_all model cls m =
  Option.bind m (fun m -> Option.map fst (enforce_constraints (List.map (constraint_of_can_clause model) cls) m))

(** [quickxplain model ~added base cls] is a minimal subset of the clauses [cls] of [model]
  inconsistent with [base] (a model, or [None] if inconsistent), assuming that [cls] is. [added]
  tells if [base] was extended since its consistency was last checked. This is QuickXplain, from
  Ulrich Junker, "QUICKXPLAIN: Preferred Explanations and Relaxations for Over-Constrained
  Problems", AAAI 2004: it makes O(k log(n/k)) consistency checks for a core of k clauses
  among n *)
let rec quickxplain model ~added base cls =
  if added && Option.is_empty base then []
  else match cls with
    | [] | [_] -> cls
    | _ ->
      let c1, c2 = CList.chop (List.length cls / 2) cls in
      let d2 = quickxplain model ~added:true (enforce_all model c1 base) c2 in
      let d1 = quickxplain model ~added:(not (CList.is_empty d2)) (enforce_all model d2 base) c1 in
      d1 @ d2

(** [explain_core model ncls] is a minimal set of clauses of [model] inconsistent with the
  clauses [ncls], among the clauses between their premises and conclusions *)
let explain_core model ncls =
  let setidx = Index.find Level.set model.table in
  let add_exprs exprs seen = NeList.fold (fun (x, _ as e) seen -> PMap.add x.canon e seen) exprs seen in
  let ends = List.fold_left (fun ends { clause = (prems, concl); _ } ->
      add_exprs (NeList.Cons (concl, prems)) ends) PMap.empty ncls in
  let all next sel =
    let starts = List.fold_left (fun acc { clause; _ } -> add_exprs (sel clause) acc) PMap.empty ncls in
    reach (fun x f -> next model x (fun ~single:_ y acc -> f y acc)) (PMap.fold (fun _ e acc -> e :: acc) starts []) starts
  in
  let above = all fold_above fst in
  let below = all fold_below (fun (_, concl) -> NeList.tip concl) in
  let above_all = PMap.mem setidx above in
  let between idx = PMap.mem idx ends ||
    ((above_all || PMap.mem idx above) && (Index.equal idx setidx || PMap.mem idx below)) in
  let zone = PMap.fold (fun idx can acc -> if between idx then (idx, can) :: acc else acc) model.entries [] in
  let cls = List.fold_left (fun acc (_, can) ->
      ClausesOf.fold (fun _local (k, prems) acc ->
          if NeList.for_all (fun (p, _) -> between (repr model p).canon) prems then
            (repr_premises model prems, (can, k)) :: acc
          else acc)
        can.clauses_bwd acc) [] zone
  in
  let base = List.fold_left (fun m (idx, _) ->
      let l = Index.repr idx model.table in
      if Level.is_set l then m else add l m) (add Level.set empty) zone in
  let base = enforce_all model (List.map (fun { clause; _ } -> clause) ncls) (Some base) in
  if Option.has_some (enforce_all model cls base) then
    (debug_loop_checking Pp.(fun () -> str "explain_core: the clauses between are consistent");
     [])
  else quickxplain model ~added:false base cls

(** The equalities of the non-canonical universes of [u] *)
let explain_aliases model u =
  Level.Set.fold (fun l acc ->
      match canonical_repr_level_expr model (l, 0) with
      | NeList.Tip (can, 0) when Level.equal l (Index.repr can.canon model.table) -> acc
      | canl -> (Universe.make l, UEq, univ_of_can_premises model canl) :: acc)
    (Universe.levels u) []

let get_explanation ((l, _, r) as cst : UnivConstraint.t) model : explanation =
  let ncls = explained_clauses model cst in
  let paths = let memo = ref [] in fun (x, k as start) ->
    match List.find_opt (fun ((y, k'), _) -> x == y && Int.equal k k') !memo with
    | Some (_, best) -> best
    | None -> let best = paths_above model start in memo := (start, best) :: !memo; best
  in
  match CList.find_map (explain_chain model paths) ncls with
  | Some chain -> chain
  | None ->
    let aliases = explain_aliases model (Universe.sup l r) in
    Constraints (aliases @ List.map (explain_can_clause model) (explain_core model ncls))

(* Precondition: all mentionned universes are canonical *)
let merge_clauses premsfwd can cank premsbwd concl conclk =
  (* New constraint: premsbwd[can + k := premsfwd + k'] -> concl + conclk']  *)
  let bk = NeList.find (fun c -> Index.equal c can) premsbwd in
  let premsfwd, premsbwd, conclk =
    (* Align the clauses on the same universe by the admissible shift transform *)
    if bk <= cank then
      (* Shift the backwards clause *)
      let diff = cank - bk in
      premsfwd, Premises.shift diff premsbwd, conclk + diff
    else
      Premises.shift (bk - cank) premsfwd, premsbwd, conclk
  in
  let prems' = NeList.map_splice (fun (c, _) ->
    if Index.equal c can then Some premsfwd else None) premsbwd in
  (prems', (concl, conclk))

let repr_clause model (prems, concl) =
  (NeList.concat_map (canonical_repr model) prems, canonical_repr model concl)

let level_expr_of_premise model (idx, k) = (Index.repr idx model.table, k)

let level_exprs_of_premises model prems =
  NeList.map (level_expr_of_premise model) prems

let univ_of_premises model u =
  Universe.unrepr (NeList.to_list (level_exprs_of_premises model u))

let repr_univ model u =
  NeList.concat_map (canonical_repr_level_expr model) (NeList.of_list (Universe.repr u))

(** Simplify u <= max (Set, v) clauses to u <= v and filter away u <= ... u + n , ... clauses, always valid. *)
let filter_trivial_clause m (prems, (concl, k as conclk)) =
  (* Trivial ... u + k + n ... -> u + k clause *)
  if NeList.exists (fun (prem, k') -> Index.equal prem concl && k' >= k) prems then None
  else
    let filter (prem, k') = not (Index.equal prem concl && k' >= k) in
    match Premises.filter filter prems with
    | None -> (* We removed the only trivial premise (concl, k') -> concl, k *) None
    | Some prems ->
      (* Filter out `Set` from max(Set, u) -> v constraints *)
      Some (remove_dominated_set Fun.id (Index.find Level.set m.table) prems, conclk)

exception InconsistentEquality

(** [set idx u model] substitutes universe [u] for all occurrences of [idx] in model, resulting
  in a set of constraints that no longer mentions [idx]. This is a stronger than [enforce_eq idx u],
  as the [idx] universe is dropped from the constraints altogether.

  @raises InconsistentEquality if one of the constraints involving [idx] cannot be satisfied when substituting [idx] with [u]. *)

(** [remove_clause_copies can model] removes from the other nodes of [model] the copies of
  the clauses of [can]: the backward copies of its forward clauses and their forward copies at
  their other premises, and the forward copies of its backward clauses. As every clause is
  registered in the forward clauses of each of its premises and in the backward clauses of its
  conclusion, these are all the clauses mentioning [can] outside [can] itself. *)
let remove_clause_copies can model =
  let canon = can.canon in
  let model =
    ForwardClauses.fold (fun ~kprem ~concl ~prems model ->
      PartialClausesOf.fold (fun (kconcl, others) model ->
        let prems = fwd_premises canon kprem others in
        let model =
          if Index.equal concl canon then model else
          let c = repr model concl in
          let bwd = ClausesOf.remove (kconcl, prems) c.clauses_bwd in
          if bwd == c.clauses_bwd then model else change_node model { c with clauses_bwd = bwd }
        in
        Premises.fold (fun (q, kq) model ->
          if Index.equal q canon then model else
          let cq = repr model q in
          let fwd = ForwardClauses.remove ~kprem:kq concl (kconcl, remove_premise q prems) cq.clauses_fwd in
          if fwd == cq.clauses_fwd then model else change_node model { cq with clauses_fwd = fwd })
          prems model)
        prems model)
      can.clauses_fwd model
  in
  ClausesOf.fold (fun _local (k, prems) model ->
    Premises.fold (fun (p, kp) model ->
      if Index.equal p canon then model else
      let cp = repr model p in
      let fwd = ForwardClauses.remove ~kprem:kp canon (k, remove_premise p prems) cp.clauses_fwd in
      if fwd == cp.clauses_fwd then model else change_node model { cp with clauses_fwd = fwd })
      prems model)
    can.clauses_bwd model

let set_can ?entailed (can,k) u model =
  let u =
    if Int.equal k 0 then u
    else
      if NeList.for_all (fun (_, k') -> k' >= k) u then
        NeList.map (fun (x, k') -> (x, k' - k)) u
      else raise InconsistentEquality
  in
  let fwd = can.clauses_fwd in
  let bwd = can.clauses_bwd in
  (* [u] can mention the same universe several times, e.g. [l, l+1]: the
     premises of the substitution mention each universe once, as expected by
     [Premises.subst] *)
  let uprems = match NeList.map (fun (can, k) -> can.canon, k) u with
    | NeList.Tip _ as p -> p
    | NeList.Cons (e, p) -> NeList.fold Premises.add p (NeList.Tip e)
  in
  debug_loop_checking_set_can Pp.(fun () ->
      str"set_can " ++ pr_index_point model (can.canon, k) ++
      str" = " ++ Premises.pr (pr_index_point model) uprems ++
      str" from fwd " ++ pr_clauses model (ForwardClauses.to_clauses
        (NeList.Tip (can.canon, 0)) fwd));
  let newfwd = UnivSubst.subst_fwd_clauses can.canon uprems fwd in
  let newbwd = UnivSubst.subst_bwd_clauses can.canon uprems bwd in
  let model = remove_clause_copies can model in
  let model = enter_equiv model can.canon can.local uprems in
  let fwdcls = ForwardClauses.to_clauses uprems newfwd in
  let bwdcls = ClausesOf.to_clauses uprems newbwd in
  let newcls = fwdcls @ List.map snd bwdcls in
  debug_loop_checking_set_can Pp.(fun () ->str "newfwd: " ++ pr_clauses model fwdcls ++
    str"bwdcls: " ++ pr_clauses model (List.map snd bwdcls));
  let newcls = List.filter_map (filter_trivial_clause model) newcls in
  match enforce_clauses ?entailed newcls model with
  | Some res -> res
  | None -> raise InconsistentEquality

exception OccurCheck
exception NotCanonical

let set_can ?entailed cank u model =
  if NeList.exists (fun (can', _k') -> fst cank == can') u then raise OccurCheck
  else
    let setidx = Index.find Level.set model.table in
    if Index.equal (fst cank).canon setidx then raise InconsistentEquality
    else
      let model, equivs = set_can ?entailed cank u model in
      let equivs = unrepr_equivalences model equivs in
      model, equivs

let clause_count m l =
  match Index.find l m.table with
  | exception Not_found -> 0
  | idx ->
    match PMap.find_opt idx m.entries with
    | Some can -> ForwardClauses.cardinal can.clauses_fwd + ClausesOf.cardinal can.clauses_bwd
    | None -> 0

let set ?entailed lvl u model =
  let cank = canonical_repr_level_expr model (lvl, 0) in
  let cank =
    match cank with
    | NeList.Tip cank -> cank
    | _ -> raise NotCanonical
  in
  let u = repr_univ model u in
  set_can ?entailed cank u model

type level_equivalences = (Level.t * (Level.t * int)) list

type 'a simplification_result =
  | HasSubst of 'a * level_equivalences * Universe.t
  | NoBound
  | CannotSimplify

(** [minimize idx model] returns a new model where the universe level idx has been set
  to its greatest lower bound and the new constraints are enough to derive the previous ones on all other universes.
  It returns a lower bound on idx in the original constraints, or None if it cannot be expressed.
  E.g. minimizing k when the only constraint is l + 1 <= k + 2 would result in k = l - 1 which is not a valid universe.  *)
let minimize_can ?(require_entailed=false) can k model =
  let fwd = can.clauses_fwd in
  let glb, multi =
    ForwardClauses.fold (fun ~kprem ~concl ~prems acc ->
      let concl = repr model concl in
      PartialClausesOf.fold (fun (conclk, premsfwd) (glb, multi) ->
        (* premsfwd, can + kprem -> concl + conclk *)
        match premsfwd with
        | None -> (concl, (conclk - kprem)) :: glb, multi
        | Some others -> glb, (concl, conclk, kprem, others) :: multi)
        prems acc)
    fwd ([], [])
  in
  let sort (idx, k) (idx', k') =
    match Index.compare idx.canon idx'.canon with
    | 0 -> Int.compare k k'
    | n -> n
  in
  let glb = List.sort_uniq sort glb in
  let glb = List.remove_assq can glb in
  if CList.is_empty glb then NoBound
  else
    if List.for_all (fun (_, k) -> k >= 0) glb
    then
      let u = NeList.of_list glb in
      (* The clauses where [can] is the only premise are its lower bounds, which become trivial,
         while its upper bounds [can + k <= max(prems)] become the clauses [glb + k <= max(prems)],
         already entailed through [can]. A clause where [can] is one of several premises,
         [v <= max(can, w)], becomes the stronger [v <= max(glb, w)]: when the model already
         entails these, setting [can] to its greatest lower bound creates no equality, no need to
         look for them *)
      let entailed (concl, conclk, kprem, others) =
        let substituted = List.map (fun (l, k) -> (l, k + kprem)) glb in
        let others = List.map (fun (idx, k) -> (repr model idx, k)) (NeList.to_list others) in
        entails model (NeList.of_list (substituted @ others)) (concl, conclk)
      in
      let entailed = List.for_all entailed multi in
      debug_loop_checking_minimize Pp.(fun () -> str"minimize_can: " ++ int (List.length multi) ++
        str" clauses with several premises, " ++ (if entailed then str"entailed" else str"not entailed"));
      (* Without entailment, the substitution strengthens a clause [v <= max(can, w)] into
         [v <= max(glb, w)]: a constraint on other universes, making them less general *)
      if require_entailed && not entailed then CannotSimplify else
      try
        let model, equivs = set_can ~entailed (can,k) u model in
        debug_check_invariants model;
        HasSubst (model, equivs, univ_of_can_expr_list model glb)
      with InconsistentEquality | OccurCheck -> CannotSimplify
    else CannotSimplify


let minimize ?require_entailed level model =
  match repr model (Index.find level model.table) with
  | exception Not_found -> CannotSimplify
  | can -> minimize_can ?require_entailed can 0 model

let maximize_can can model =
  let bwd = can.clauses_bwd in
  let card = ClausesOf.cardinal bwd in
  match card with
  | 0 -> NoBound
  | n when n <> 1 -> CannotSimplify
  | _ ->
    let cank, ubound = ClausesOf.choose bwd in
    if NeList.for_all (fun (_, k) -> cank <= k) ubound then
      let ubound = NeList.map (fun (can, k) -> (can, k - cank)) ubound in
      let ubound = repr_premises model ubound in
      try
        let model, equivs = set_can (can, 0) ubound model in
        HasSubst (model, equivs, univ_of_can_premises model ubound)
      with InconsistentEquality | OccurCheck -> CannotSimplify
    else CannotSimplify

let maximize level model =
  match repr model (Index.find level model.table) with
  | exception Not_found -> CannotSimplify
  | can -> maximize_can can model

let has_upper_bound level model =
  match repr model (Index.find level model.table) with
  | exception Not_found -> true
  | can -> not (ClausesOf.is_empty can.clauses_bwd)

let lower_bound level model =
  match repr model (Index.find level model.table) with
  | exception Not_found -> None
  | can ->
    let glb =
      ForwardClauses.fold (fun ~kprem ~concl ~prems glb ->
          let concl = repr model concl in
          PartialClausesOf.fold (fun (conclk, premsfwd) glb ->
              if Option.is_empty premsfwd then (concl, conclk - kprem) :: glb else glb)
            prems glb)
        can.clauses_fwd []
    in
    let sort (idx, k) (idx', k') =
      match Index.compare idx.canon idx'.canon with 0 -> Int.compare k k' | n -> n
    in
    match List.remove_assq can (List.sort_uniq sort glb) with
    | [] -> None
    | glb -> Some (univ_of_can_expr_list model glb)

let substitution_entailed subst model =
  let find l = repr model (Index.find l model.table) in
  match List.map (fun (u, v) -> find u, find v) subst with
  | exception Not_found -> false
  | subst ->
    let sigma can =
      match List.find_opt (fun (u, _) -> Index.equal u.canon can.canon) subst with
      | Some (_, v) -> v
      | None -> can
    in
    let holds prems (concl, k) =
      let prems = NeList.map (fun (p, kp) -> (sigma p, kp)) prems in
      entails model prems (sigma concl, k)
    in
    let clauses_hold (u, _) =
      (* The clauses [concl + k <= max(u + kprem, others)] *)
      ForwardClauses.fold (fun ~kprem ~concl ~prems ok ->
          ok && PartialClausesOf.fold (fun (conclk, premsfwd) ok ->
              ok &&
              let others = match premsfwd with
                | None -> []
                | Some others -> List.map (fun (idx, k) -> (repr model idx, k)) (NeList.to_list others)
              in
              holds (NeList.of_list ((u, kprem) :: others)) (repr model concl, conclk))
            prems true)
        u.clauses_fwd true &&
      (* The clauses [u + k <= max(prems)] *)
      ClausesOf.fold (fun _local (k, prems) ok ->
          ok && holds (NeList.map (fun (idx, kp) -> (repr model idx, kp)) prems) (u, k))
        u.clauses_bwd true
    in
    List.for_all clauses_hold subst

(** [remove_can_clause m cl] removes the local clause [cl], canonical and simplified as by
  [simplify_can_clause], from the backward clauses of its conclusion and the forward clauses of its
  premises, where [add_can_clause_model] added it; [None] if [m] does not have it locally. The
  values of [m] are still a model of the remaining clauses. *)
let remove_can_clause m ((prems, (concl, conclk)) : can_clause) =
  let canl = repr m concl.canon in
  let canprems = NeList.map (fun (can, k) -> (can.canon, k)) prems in
  let clof = (conclk, canprems) in
  let bwd = canl.clauses_bwd in
  if not (ClausesOf.SWC.mem clof bwd.ClausesOf.local) then None else
  let bwd = { bwd with ClausesOf.local = ClausesOf.SWC.remove clof bwd.ClausesOf.local } in
  let m = change_node m { canl with clauses_bwd = bwd } in
  Some (NeList.fold (fun (prem, kprem) m ->
      let idx = repr m prem.canon in
      let fwd = ForwardClauses.remove ~kprem canl.canon (conclk, remove_premise prem.canon canprems)
          idx.clauses_fwd in
      if fwd == idx.clauses_fwd then m else change_node m { idx with clauses_fwd = fwd })
      prems m)

let remove_if_entailed cst m =
  match clauses_of_constraint m cst with
  | exception Undeclared _ -> None
  | cls ->
    (* As in [enforce_clauses], a conclusion substituted by [max(a, b)] gives a clause for each *)
    let cls = List.concat_map (fun (prems, concl) ->
        let prems = canonical_premises_repr m prems in
        NeList.to_list (NeList.map (fun concl -> (prems, repr_expr m concl))
                          (canonical_can_premises (canonical_repr m concl)))) cls in
    let simplify cl = match simplify_can_clause m cl with
      | Canonical cl -> Some (Some cl)
      | Trivial -> None
      | Contradictory -> Some None
    in
    let cls = List.filter_map simplify cls in
    if List.exists Option.is_empty cls then None else
    let cls = List.map Option.get cls in
    let removed = List.fold_left (fun m cl -> Option.bind m (fun m -> remove_can_clause m cl))
        (Some m) cls in
    Option.bind removed (fun m' ->
        let refresh (can, k) = (repr m' can.canon, k) in
        if List.for_all (fun (prems, concl) -> entails m' (NeList.map refresh prems) (refresh concl)) cls
        then Some m' else None)

let remove_bwd_clauses_from model idx k other =
  let can = repr model idx in
  let bwd = can.clauses_bwd in
  let bwd' = ClausesOf.filter (fun (kconcl, prems) ->
    not (Int.equal kconcl k) ||
    match prems with
    | NeList.Tip (prem, 0) -> not (Index.equal prem other)
    | _ -> true) bwd
  in
  change_node model { can with clauses_bwd = bwd' }

let replace_bwd prems kprem concl clsof =
  ForwardClauses.replace { prems; kprem; concl } clsof

let remove_set_clauses_can can model =
  let setidx = Index.find Level.set model.table in
  let fwd = can.clauses_fwd in
  match ForwardClauses.IntMap.find 0 fwd with
  | exception Not_found -> model
  | fwd_clauses ->
    match ForwardClauses.PMap.find setidx fwd_clauses with
    | exception Not_found -> model
    | prems ->
      let prems = PartialClausesOf.filter_map
      (fun (k', prem as x) ->
        if Int.equal k' 0 && Option.is_empty prem then None else Some x)
        prems
      in
      let fwd = replace_bwd prems 0 setidx fwd in
      let model = change_node model { can with clauses_fwd = fwd } in
      (* Filter out u -> Set + 0 constraints *)
      remove_bwd_clauses_from model setidx 0 can.canon

let remove_set_clauses l model =
  match repr model (Index.find l model.table) with
  | exception Not_found -> model
  | can -> remove_set_clauses_can can model

let constraint_type_ord c1 c2 = match c1, c2 with
| UnivConstraint.Le, UnivConstraint.Le -> 0
| UnivConstraint.Le, UnivConstraint.Eq -> -1
| UnivConstraint.Eq, UnivConstraint.Eq -> 0
| UnivConstraint.Eq, UnivConstraint.Le -> 1

type univ_constraint = Universe.t * UnivConstraint.kind * Universe.t

module UConstraintOrd =
struct
type t = univ_constraint
let compare (u,c,v) (u',c',v') =
  let i = constraint_type_ord c c' in
  if not (Int.equal i 0) then i
  else
    let i' = Universe.compare u u' in
    if not (Int.equal i' 0) then i'
    else Universe.compare v v'
end


module Constraints =
struct
  module S = Set.Make(UConstraintOrd)
  include S

end

let subst ~local model =
  PMap.fold (fun idx { alias_prems = v; alias_local = locality; alias_local_eq = locality_eq; _ } acc ->
    if not local || (local && locality_eq == Local) then
      let conclp = Index.repr idx model.table in
      let node = univ_of_premises model v in
      Level.Map.add conclp (locality, node) acc
    else acc)
  model.subst Level.Map.empty

let constraint_of_clause m concl (k, prems) =
  let prems = NeList.to_list prems in
  let prems =
    List.map (fun (v, k) ->
      let vcan = repr m v in
      let vp = Index.repr vcan.canon m.table in
      (vp, k)) prems
  in
  let prem = Universe.unrepr prems in
  (Universe.of_list [(Index.repr concl m.table, k)], UnivConstraint.Le, prem)

let constraints_of model ?(only_local = false) fold acc =
  (* With [only_local], most nodes of a graph extending the global one have no local clauses:
     only their local clauses are visited *)
  let constraints_of _u can (locals, cstrs) =
    let locals =
      if only_local && can.local == Local then Level.Set.add (Index.repr can.canon model.table) locals
      else locals
    in
    let add cl cstrs = Constraints.add (constraint_of_clause model can.canon cl) cstrs in
    let cstrs =
      if only_local then ClausesOf.fold_local add can.clauses_bwd cstrs
      else ClausesOf.fold (fun _local -> add) can.clauses_bwd cstrs
    in
    locals, cstrs
  in
  let init = (Level.Set.empty, Constraints.empty) in
  let locals, cstrs =
    if only_local then
      (* Only the nodes which can be local or have local clauses *)
      Index.Set.fold (fun idx acc -> match PMap.find_opt idx model.entries with
          | Some can -> constraints_of idx can acc
          | None -> acc) model.locals init
    else PMap.fold constraints_of model.entries init
  in
  let equivs_of u { alias_prems = v; alias_local = local; alias_local_eq = local_eq; _ } equiv =
    if only_local && local_eq == Global then equiv else
    let u = Index.repr u model.table in
    let v = univ_of_premises model v in
    Level.Map.add u (local, v) equiv
  in
  let equiv =
    if only_local then
      Index.Set.fold (fun u equiv -> match PMap.find_opt u model.subst with
          | Some e -> equivs_of u e equiv
          | None -> equiv) model.local_eqs Level.Map.empty
    else PMap.fold equivs_of model.subst Level.Map.empty
  in
  locals, Constraints.fold fold cstrs acc, equiv

type 'a constraint_fold = univ_constraint -> 'a -> 'a

let interp_univ model l =
  Universe.of_list (NeList.to_list (NeList.map (fun (idx, k) -> (Index.repr idx model.table, k)) l))

(* A clause u + k, ... -> v + k' is trivial if u = v and k >= k'. or v = 0 and k >= k' *)
let is_trivial setidx u k v k' =
  (Index.equal u v && k >= k') ||
  (Index.equal v setidx && k >= k')

(** [eliminate_can ~alive ~skip_set model idx] adds to [model] the resolvents on the canonical
  universe [idx] of its clauses: each pair of clauses [premsbwd -> idx + cank] and
  [idx + kprem, premsfwd -> concl + conclk] gives the clause [premsbwd, premsfwd -> concl + conclk]
  (up to the shifts aligning [idx + cank] and [idx + kprem]), which does not mention [idx].
  The clauses that do not mention [idx] then derive all the consequences of [model] that
  do not mention it (Fourier-Motzkin elimination). Only the clauses whose other universes are
  [alive] are considered, so that the resolvents only mention [alive] universes.
  The clauses of [idx] are left in the model.
  If [skip_set], the always valid clauses [idx + kprem, ... -> Set + conclk] with [kprem >= conclk]
  are ignored. *)
let eliminate_can ~alive ~skip_set model idx =
  let can = repr model idx in
  assert (Index.equal can.canon idx);
  let setidx = Index.find Level.set model.table in
  let alive_prems prems = Premises.for_all (fun (idx', _) -> alive idx') prems in
  (* [premsbwd, idx + k -> idx + cank] with [k < cank] is equivalent to [premsbwd -> idx + cank] *)
  let bwd = ClausesOf.fold (fun _local (cank, premsbwd) bwd ->
      match Premises.filter (fun (idx', _) -> not (Index.equal idx idx')) premsbwd with
      | Some premsbwd when alive_prems premsbwd -> (cank, premsbwd) :: bwd
      | _ -> bwd)
      can.clauses_bwd []
  in
  match bwd with
  | [] -> model
  | _ ->
  ForwardClauses.fold (fun ~kprem ~concl ~prems model ->
    (* The clauses concluding [idx] are considered as backward clauses above *)
    if Index.equal concl idx || not (alive concl) then model else
    PartialClausesOf.fold (fun (conclk, premsfwd) model ->
      (* premsfwd, idx + kprem -> concl + conclk *)
      if skip_set && Index.equal concl setidx && kprem >= conclk then model
      else if not (Option.cata alive_prems true premsfwd) then model else
      let premsfwd = cons_opt_nelist (idx, kprem) premsfwd in
      List.fold_left (fun model (cank, premsbwd) ->
        (* premsbwd -> idx + cank *)
        let cl = merge_clauses premsbwd idx cank premsfwd concl conclk in
        let cl =
          match repr_clause model cl with
          | (prems, NeList.Tip concl) -> (prems, concl)
          | _ -> assert false (* The conclusion was already canonical, cannot expand to a list of universes *)
        in
        match simplify_can_clause model cl with
        | Trivial -> model
        | Contradictory -> assert false
        | Canonical cl ->
          if subsumed ~alive cl then model else
          match add_can_clause_model model cl with
          | Some (_, m) -> m
          | None -> model)
        model bwd)
      prems model)
    can.clauses_fwd model

(** [closure succs seeds] is the set of universes reachable from [seeds] through [succs] *)
let closure succs seeds =
  let rec aux todo visited =
    match todo with
    | [] -> visited
    | idx :: todo ->
      let todo, visited = succs idx (fun idx' (todo, visited as acc) ->
          if PSet.mem idx' visited then acc else (idx' :: todo, PSet.add idx' visited))
          (todo, visited)
      in
      aux todo visited
  in aux (PSet.elements seeds) seeds

(** [spanned_subgraph ~skip_set model kept] is the set of universes of the subgraph spanned
  by the canonical universes [kept]: those above some kept universe through clauses whose
  premises are all below some kept universe. Only these universes can appear in the derivation
  of a clause between kept universes.
  If [skip_set], the always valid clauses [Set + k <= max(..., u + k', ...)] with [k' >= k]
  are ignored. *)
let spanned_subgraph ~skip_set model kept =
  let setidx = Index.find Level.set model.table in
  let trivial concl k prems =
    skip_set && Premises.exists (fun (u, ku) -> is_trivial setidx u ku concl k) prems
  in
  (* The universes below some kept universe [v]: [u + k <= max(..., v + k', ...)] or
     [u + k <= max(..., u' + k', ...)] with [u'] below [v]. All the premises of a clause need not
     be below a kept universe: e.g. from [x + 1 <= max(p, b)] and [p + 1 <= max(x, b')], [x] is
     bounded by [b] and [b'], [x + 2 <= max(b + 1, b')], while none of these clauses has all its
     premises bounded. *)
  let below = closure (fun idx f acc ->
      ForwardClauses.fold (fun ~kprem ~concl ~prems acc ->
        if PartialClausesOf.exists (fun (conclk, others) ->
            not (trivial concl conclk (fwd_premises idx kprem others))) prems
        then f concl acc else acc)
        (repr model idx).clauses_fwd acc)
      kept
  in
  closure (fun idx f acc ->
      ClausesOf.fold (fun _local (k, prems) acc ->
        if trivial idx k prems || not (Premises.for_all (fun (u, _) -> PSet.mem u below) prems) then acc
        else NeList.fold (fun (u, _) acc -> f u acc) prems acc)
        (repr model idx).clauses_bwd acc)
    kept

(** [eliminate_spanned ~skip_set model kept] eliminates the universes of the subgraph spanned by
  the canonical universes [kept] that are not [kept] (see [eliminate_can]). Afterwards, the clauses
  between [kept] universes derive all the clauses between them derivable in [model]. *)
let eliminate_spanned ~skip_set model kept =
  let spanned = spanned_subgraph ~skip_set model kept in
  let removed = PSet.filter (fun idx -> not (PSet.mem idx kept)) spanned in
  let model, _ = PSet.fold (fun idx (model, alive) ->
      let alive = PSet.remove idx alive in
      eliminate_can ~alive:(fun idx -> PSet.mem idx alive) ~skip_set model idx, alive)
      removed (model, spanned)
  in
  model

(** [constraints_for ~kept model] computes the constraints between the [kept] universes
  derivable in [model]. Only the subgraph spanned by the kept universes is considered
  (see [spanned_subgraph]): the removed universes of that subgraph are eliminated, the
  other ones are ignored. *)
let constraints_for ~(kept:Level.Set.t) model (fold : 'a constraint_fold) (accu : 'a) : 'a =
  let add_cst u knd v (cst : 'a) : 'a =
    fold (interp_univ model u, knd, interp_univ model v) cst
  in
  (* The canonical node [can] and shift [k] of each kept universe [u = can + k] *)
  let keptp = Level.Set.fold (fun u keptp ->
      let idx = Index.find u model.table in
      match canonical_repr model (idx, 0) with
      | NeList.Tip (can, k) -> PMap.add idx (can.canon, k) keptp
      | NeList.Cons _ -> raise NotCanonical)
      kept PMap.empty
  in
  (* rmap: map from the canonical nodes of the kept universes to a kept universe [v]
     representing them, such that [v = can + k] *)
  let rmap = PMap.fold (fun u (can, k) rmap ->
      if PMap.mem can keptp then PMap.add can (can, 0) rmap
      else match PMap.find_opt can rmap with
        | Some (_, k') when k' <= k -> rmap
        | _ -> PMap.add can (u, k) rmap)
      keptp PMap.empty
  in
  let is_kept idx = PMap.mem idx rmap in
  (* [can + j] is [v + j - k] *)
  let rexpr (can, j) = let (v, k) = PMap.find can rmap in (v, j - k) in
  let add_shifted_cst l knd r csts =
    let min_shift prems m = NeList.fold (fun (_, k) m -> min k m) prems m in
    let shift = min_shift l (min_shift r 0) in
    let l, r = if shift < 0 then Premises.shift (- shift) l, Premises.shift (- shift) r else l, r in
    add_cst l knd r csts
  in
  let kept_cans = PMap.fold (fun can _ acc -> PSet.add can acc) rmap PSet.empty in
  let model = eliminate_spanned ~skip_set:true model kept_cans in
  let csts = PMap.fold (fun u (can, k) csts ->
      if Index.equal u (fst (PMap.find can rmap)) then csts
      else add_shifted_cst (NeList.tip (u, 0)) UnivConstraint.Eq (NeList.tip (rexpr (can, k))) csts)
      keptp accu
  in
  PMap.fold (fun can _ csts ->
      ClausesOf.fold (fun _local (k, prems) csts ->
        if Premises.for_all (fun (u, _) -> is_kept u) prems then
          add_shifted_cst (NeList.tip (rexpr (can, k))) UnivConstraint.Le (NeList.map rexpr prems) csts
        else csts)
        (repr model can).clauses_bwd csts)
    rmap csts

let domain model = Index.dom model.table

let variables ~local ~with_subst model =
  let entries = if local then PMap.filter (fun _ can -> can.local == Local) model.entries else model.entries in
  let canon =
    let add idx _ = Level.Set.add (Index.repr idx model.table) in
    Index.Map.fold add entries Level.Set.empty
  in
  if with_subst then
    let add idx { alias_local = locality; _ } acc =
      if not local || locality == Local then
        Level.Set.add (Index.repr idx model.table) acc
      else acc
    in
    PMap.fold add model.subst canon
  else canon

type node =
| Alias of Universe.t
| Node of (int * Universe.t) list (** Nodes [(k_i, u_i); ...] s.t. u + k_i <= u_i *)

type model_repr = node Level.Map.t


let univ_of_expr model (l, k) =
  Universe.of_expr (Index.repr l model.table, k)

let universe_of_premise model prem =
  match prem with
  | NeList.Tip (l, k) -> univ_of_expr model (l, k)
  | NeList.Cons (e, xs) ->
    NeList.fold (fun (l, k) acc -> Universe.sup (univ_of_expr model (l, k)) acc) xs (univ_of_expr model e)

let model_repr ~local model =
  let acc =
    PMap.fold (fun idx can acc ->
      let conclp = Index.repr idx model.table in
      let prems = can.clauses_bwd in
      let cls =
        ClausesOf.fold (fun locality cli l ->
          let (k, prem) = cli in
          if not local || (local && locality == Local) then
            let u = universe_of_premise model prem in
            (k, u) :: l
          else l) prems []
        in
      if local && can.local == Global && CList.is_empty cls then acc
      else Level.Map.add conclp (Node cls) acc)
    model.entries Level.Map.empty
  in
  PMap.fold (fun idx { alias_prems = v; alias_local_eq = locality_eq; _ } acc ->
    if not local || (local && locality_eq == Local) then
      let conclp = Index.repr idx model.table in
      let node = Alias (univ_of_premises model v) in
      Level.Map.add conclp node acc
    else acc)
  model.subst acc

let pmap_to_point_map table pmap =
  PMap.fold (fun idx v acc ->
    let p = Index.repr idx table in
    Level.Map.add p v acc)
    pmap Level.Map.empty

(** [valuation_of_model m] is the valuation of the universes in the natural numbers given by the
  model [m], as in MetaRocq: values may be negative, and are shifted by the value of [Set], the
  largest one as [Set] is below all universes. A universe [u] of value [v] is mapped to
  [value(Set) - v], and an alias [u = max(e_i + k_i)] to the maximum of the [e_i + k_i]. *)
let valuation_of_model (m : model) =
  let setv = Option.get (canonical_value m (PMap.find (Index.find Level.set m.table) m.entries)) in
  let valm = PMap.map (fun e -> setv - Option.get (canonical_value m e)) m.entries in
  let equivsm = PMap.map (fun { alias_prems = v; _ } ->
    let expr_valuation (e, k) = setv - Option.get (canonical_value m e) + k in
    Premises.fold_ne (fun e acc -> max (expr_valuation e) acc) expr_valuation (repr_premises m v)) m.subst
  in
  Level.Map.union (fun _ x y -> Some (max x y))
    (pmap_to_point_map m.table valm)
    (pmap_to_point_map m.table equivsm)

let valuation model = valuation_of_model model

(** {2 Removal of universes}

  [remove removed model] removes the [removed] universes from [model], keeping the constraints
  between the other ones that they entail. Either the removed universes are eliminated one by one
  (Fourier-Motzkin elimination, [remove_eliminating]), or, when most universes are removed, the
  model is rebuilt from the subgraph spanned by the kept ones ([remove_restricting]). *)

let occurs_in_premises removed prems =
  Premises.exists (fun (idx', _) -> removed idx') prems

(** [remove_from_fwd removed fwd] and [remove_from_bwd removed bwd] remove the clauses mentioning
  universes satisfying [removed] *)
let remove_from_fwd removed fwd =
  let f _kprem concl prems =
    if removed concl then None
    else
      let prems = PartialClausesOf.filter (fun (_kconcl, prems) ->
        match prems with
        | None -> true
        | Some prems -> not (occurs_in_premises removed prems))
        prems
      in
      if PartialClausesOf.is_empty prems then None else Some prems
  in
  ForwardClauses.filter_map f fwd

let remove_from_bwd removed bwd =
  let f (_kconcl, prems) = not (occurs_in_premises removed prems) in
  ClausesOf.filter f bwd

(** [remove_from_model idxs model] Removes all clauses mentionning [idxs] and
  the canonical nodes for [idxs] from the model. The substitution is also filtered to not mention [idxs].
  The levels are still registered in the [Index] table, for possible reuse (see [add_model]) *)
let remove_from_model idxs model =
  (* The clauses mentioning [idxs] are all registered in the clauses of [idxs]:
     only the nodes of their other universes need to be filtered *)
  let add_prems prems acc = NeList.fold (fun (idx', _) acc -> PSet.add idx' acc) prems acc in
  let neighbors = PSet.fold (fun idx acc ->
      let can = repr model idx in
      let acc = ForwardClauses.fold (fun ~kprem:_ ~concl ~prems acc ->
          PartialClausesOf.fold (fun (_, others) acc -> Option.fold_right add_prems others acc)
            prems (PSet.add concl acc))
          can.clauses_fwd acc
      in
      ClausesOf.fold (fun _local (_, prems) acc -> add_prems prems acc) can.clauses_bwd acc)
      idxs PSet.empty
  in
  let removed idx = PSet.mem idx idxs in
  let f idx' entries =
    if removed idx' then entries
    else
      let can = repr model idx' in
      let clauses_fwd = remove_from_fwd removed can.clauses_fwd in
      let clauses_bwd = remove_from_bwd removed can.clauses_bwd in
      PMap.add idx' { can with clauses_fwd; clauses_bwd } entries
  in
  let entries = PSet.fold f neighbors model.entries in
  let entries = PSet.fold PMap.remove idxs entries in
  (* The substitutions mentioning [idxs] are found in [subst_deps] *)
  let feq idx (subst, subst_deps) =
    let ws = Option.default Index.Set.empty (PMap.find_opt idx subst_deps) in
    let subst, subst_deps = Index.Set.fold (fun w (subst, subst_deps as acc) ->
        match PMap.find_opt w subst with
        | None -> acc
        | Some { alias_prems = u; _ } -> PMap.remove w subst, remove_subst_deps w u subst_deps)
        ws (subst, subst_deps)
    in
    subst, PMap.remove idx subst_deps
  in
  let subst, subst_deps = PSet.fold feq idxs (model.subst, model.subst_deps) in
  { model with entries; subst; subst_deps; canonical = model.canonical - PSet.cardinal idxs }

(** [remove_eliminating removed model] eliminates the [removed] universes one by one
  (see [eliminate_can]) before removing their nodes and clauses: the cost is proportional
  to the number of removed universes. *)
let remove_eliminating removed model =
  let removed = Level.Set.fold (fun u accu -> PSet.add (Index.find u model.table) accu) removed PSet.empty in
  (* The removed aliases are dropped from the substitution *)
  let removed, subst, subst_deps =
    let remove_from_subst idx (removed, subst, subst_deps as acc) =
      match PMap.find_opt idx subst with
      | None -> acc
      | Some { alias_prems = u; _ } -> (PSet.remove idx removed, PMap.remove idx subst, remove_subst_deps idx u subst_deps)
    in
    PSet.fold remove_from_subst removed (removed, model.subst, model.subst_deps)
  in
  (* After the elimination of the removed universes, the clauses that don't mention them
     are enough to derive the clauses between kept universes. The clauses mentioning already
     eliminated universes are removed below, so they are not used for the next eliminations. *)
  let model, _ = PSet.fold (fun idx (model, eliminated) ->
      let eliminated = PSet.add idx eliminated in
      eliminate_can ~alive:(fun idx -> not (PSet.mem idx eliminated)) ~skip_set:false model idx, eliminated)
      removed ({ model with subst; subst_deps }, PSet.empty)
  in
  remove_from_model removed model

(** [remove_restricting removed model] computes the same model as [remove_eliminating], from
  the kept universes: only the removed universes of the subgraph spanned by the kept ones
  are eliminated, and the model is rebuilt from the kept nodes. The other removed universes
  are never considered, which is faster when most universes are removed. *)
let remove_restricting removed model =
  let is_removed idx = Level.Set.mem (Index.repr idx model.table) removed in
  let kept = PMap.fold (fun idx _ kept -> if is_removed idx then kept else PSet.add idx kept)
      model.entries PSet.empty
  in
  let model = eliminate_spanned ~skip_set:false model kept in
  let removed_can idx = not (PSet.mem idx kept) in
  let add_kept idx entries =
    let can = repr model idx in
    let clauses_fwd = remove_from_fwd removed_can can.clauses_fwd in
    let clauses_bwd = remove_from_bwd removed_can can.clauses_bwd in
    PMap.add idx { can with clauses_fwd; clauses_bwd } entries
  in
  let entries = PSet.fold add_kept kept PMap.empty in
  (* The removed aliases and the aliases of removed universes are dropped *)
  let subst = PMap.filter (fun idx { alias_prems = u; _ } ->
      not (is_removed idx) && not (occurs_in_premises removed_can u))
      model.subst
  in
  { model with entries; subst; subst_deps = subst_deps_of subst; canonical = PSet.cardinal kept }

let remove_core removed model =
  (* Each removed universe costs more to [remove_eliminating] than each canonical node
     of the model to [remove_restricting] *)
  if 2 * Level.Set.cardinal removed > model.canonical then remove_restricting removed model
  else remove_eliminating removed model

(** The universes adjacent to the canonical node [can] in the clauses *)
let neighbors_of can acc =
  let add_prems prems acc = NeList.fold (fun (idx', _) acc -> Index.Set.add idx' acc) prems acc in
  let acc = ForwardClauses.fold (fun ~kprem:_ ~concl ~prems acc ->
      PartialClausesOf.fold (fun (_, others) acc -> Option.fold_right add_prems others acc)
        prems (Index.Set.add concl acc))
      can.clauses_fwd acc
  in
  ClausesOf.fold (fun _local (_, prems) acc -> add_prems prems acc) can.clauses_bwd acc

(** [remove removed model] also keeps the kept aliases [w = c + k] of a removed canonical node
  [c] (the orphans): removing [c] drops them, and with them their equalities and the
  constraints of [c]. E.g. with [a = l + 1] and [b = l + 1], removing [l] loses [a = b] and
  [1 <= a]. The [c]s with orphans are removed after the other universes, so that their clauses
  then mention kept universes only. Their constraints are translated to the orphans by
  [constraints_for], which represents [c] by the orphan of least shift, and are enforced again
  on the orphans once [c] is removed. Only the rigid aliases are kept this way: the flexible ones
  are substituted in the terms (see [normalize_flexible]), so they are no longer universes of
  the context. The aliases by an algebraic universe mentioning a removed one are still dropped. *)
let remove removed model =
  let removed_idx =
    Level.Set.fold (fun u acc -> Index.Set.add (Index.find u model.table) acc) removed Index.Set.empty
  in
  let orphans_of idx =
    match PMap.find_opt idx model.subst_deps with
    | None -> Index.Set.empty
    | Some ws ->
      Index.Set.filter (fun w ->
          not (Index.Set.mem w removed_idx) &&
          match PMap.find_opt w model.subst with
          | Some { alias_prems = NeList.Tip (c, _); alias_rigid = true; _ } -> Index.equal c idx
          | Some _ | None -> false)
        ws
  in
  let held, orphans = Index.Set.fold (fun idx (held, orphans as acc) ->
      if not (PMap.mem idx model.entries) then acc
      else
        let ws = orphans_of idx in
        if Index.Set.is_empty ws then acc
        else (Index.Set.add idx held, Index.Set.union ws orphans))
      removed_idx (Index.Set.empty, Index.Set.empty)
  in
  if Index.Set.is_empty orphans then remove_core removed model
  else
    let levels_of idxs = Index.Set.fold (fun idx acc -> Level.Set.add (Index.repr idx model.table) acc) idxs Level.Set.empty in
    let held_levels = levels_of held in
    let aliases = Index.Set.fold (fun w acc -> PMap.add w (PMap.find w model.subst) acc) orphans PMap.empty in
    let model = remove_core (Level.Set.diff removed held_levels) model in
    let neighbors = Index.Set.fold (fun idx acc -> neighbors_of (repr model idx) acc) held Index.Set.empty in
    let kept = levels_of (Index.Set.union orphans (Index.Set.diff neighbors held)) in
    let cstrs = constraints_for ~kept model (fun cst acc -> cst :: acc) [] in
    let model = remove_core held_levels model in
    let model = PMap.fold (fun w alias model ->
        let _, model = add_model ~rigid:alias.alias_rigid (Index.repr w model.table) model in
        change_node model { (repr model w) with local = alias.alias_local })
        aliases model
    in
    match enforce_constraints cstrs model with
    | Some (model, _equivs) -> model
    | None -> CErrors.anomaly Pp.(str "Loop_checking.remove: the constraints of the kept aliases are inconsistent.")

(** {2 Local / global and flexible / rigid universes}

  A graph extending a global one (see [set_local]) distinguishes the universes, clauses and
  equations added since, which are local, from the global ones. The universe state of the
  elaborator is such a graph: its universe variables are its local universes, and the universes
  declared globally by side effects are made global (see [set_locality]).

  A universe is also rigid or flexible (see [add]): the flexible universes are the local
  canonical universes which are not rigid, the unification variables of the elaborator. When a
  universe is made equal to another one, the rigid one is preferably kept canonical, and only
  the non-rigid aliases are substituted in terms (see [normalize_flexible]). *)

let set_locality local l m =
  match Index.find l m.table with
  | exception Not_found -> m
  | idx ->
    match PMap.find_opt idx m.entries with
    | Some can -> if can.local == local then m else change_node m { can with local }
    | None ->
      match PMap.find_opt idx m.subst with
      | None -> m
      | Some alias ->
        match local with
        | Global ->
          if alias.alias_local == Global then m
          else { m with subst = PMap.add idx { alias with alias_local = Global } m.subst }
        | Local ->
          (* The equation of a local universe is local too *)
          if alias.alias_local == Local && alias.alias_local_eq == Local then m
          else { m with subst = PMap.add idx { alias with alias_local = Local; alias_local_eq = Local } m.subst;
                        local_eqs = Index.Set.add idx m.local_eqs }

let with_locality local f m =
  Option.map (fun (m', x) -> { m' with locality = m.locality }, x) (f { m with locality = local })

let enforce_global_constraints csts m = with_locality Global (enforce_constraints csts) m

let flip_locality = function Global -> Local | Local -> Global

let switch_locality l model =
  let can = repr model (Index.find l model.table) in
  change_node model { can with local = flip_locality can.local }

type local_status = NotLocal | LocalNode | LocalAlias

let local_status model l =
  match Index.find l model.table with
  | exception Not_found -> NotLocal
  | idx ->
    match PMap.find_opt idx model.entries with
    | Some can -> if can.local == Local then LocalNode else NotLocal
    | None ->
      match PMap.find_opt idx model.subst with
      | Some { alias_local_eq = locality_eq; _ } -> if locality_eq == Local then LocalAlias else NotLocal
      | None -> NotLocal

let is_local model l =
  let idx = Index.find l model.table in
  try let can = repr model idx in
    can.local == Local
  with Not_found ->
    let { alias_local = local; _ } = PMap.find idx model.subst in
    local == Local

let normalize_flexible m l =
  match Index.find l m.table with
  | exception Not_found -> None
  | idx ->
    match PMap.find idx m.entries with
    | _can -> None (* Already in canonical form *)
    | exception Not_found ->
      match PMap.find idx m.subst with
      | { alias_prems = p; alias_rigid = false; _ } -> Some (univ_of_premises m p) (* [p] is canonical *)
      | { alias_rigid = true; _ } -> None
      | exception Not_found -> None

let alias_rigidity m l =
  match Index.find l m.table with
  | exception Not_found -> None
  | idx ->
    match PMap.find_opt idx m.subst with
    | Some alias -> Some alias.alias_rigid
    | None -> None

(* The flexible universes are the local canonical nodes which are not rigid: the unification
   variables of the elaborator. A substituted universe is no longer flexible. *)
let is_flexible_node can = can.local == Local && not can.rigid

let is_flexible m l =
  match Index.find l m.table with
  | exception Not_found -> false
  | idx ->
    match PMap.find_opt idx m.entries with
    | Some can -> is_flexible_node can
    | None -> false

let flexible_local_levels m =
  Index.Set.fold (fun idx acc ->
      match PMap.find_opt idx m.entries with
      | Some can when is_flexible_node can -> Level.Set.add (Index.repr idx m.table) acc
      | Some _ | None -> acc)
    m.locals Level.Set.empty

let set_rigid rigid l m =
  match Index.find l m.table with
  | exception Not_found -> m
  | idx ->
    match PMap.find_opt idx m.entries with
    | Some can -> if can.rigid == rigid then m else change_node m { can with rigid }
    | None ->
      match PMap.find_opt idx m.subst with
      | Some alias when alias.alias_rigid != rigid ->
        { m with subst = PMap.add idx { alias with alias_rigid = rigid } m.subst }
      | Some _ | None -> m

(* The universes of the context of the elaborator: the local canonical nodes, and the local
   rigid aliases, which stay in the terms. The local non-rigid aliases are substituted. *)
let is_context_alias alias = alias.alias_local == Local && alias.alias_rigid

let is_context_level m l =
  match Index.find l m.table with
  | exception Not_found -> false
  | idx ->
    match PMap.find_opt idx m.entries with
    | Some can -> can.local == Local
    | None ->
      match PMap.find_opt idx m.subst with
      | Some alias -> is_context_alias alias
      | None -> false

let local_levels_gen ~only_rigid m =
  let add_level idx acc = Level.Set.add (Index.repr idx m.table) acc in
  let canon = Index.Set.fold (fun idx acc ->
      match PMap.find_opt idx m.entries with
      | Some can when can.local == Local && (can.rigid || not only_rigid) -> add_level idx acc
      | Some _ | None -> acc)
      m.locals Level.Set.empty
  in
  (* The context aliases are rigid *)
  Index.Set.fold (fun idx acc ->
      match PMap.find_opt idx m.subst with
      | Some alias when is_context_alias alias -> add_level idx acc
      | Some _ | None -> acc)
    m.local_eqs canon

let local_levels m = local_levels_gen ~only_rigid:false m

let rigid_local_levels m = local_levels_gen ~only_rigid:true m

module Internal =
struct
  let check_invariants = check_invariants
  let remove = remove
  let remove_set_clauses = remove_set_clauses
end
