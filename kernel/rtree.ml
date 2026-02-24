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

(* Type of regular trees:
   - Var denotes tree variables (like de Bruijn indices)
     the first int is the depth of the occurrence, and the second int
     is the index in the array of trees introduced at that depth.
     Warning: Var's indices both start at 0!
   - Node denotes the usual tree node, labelled with 'a, to the
     exception that it takes an array of arrays as argument
   - Rec(j,v1..vn) introduces infinite tree. It denotes
     v(j+1) with parameters 0..n-1 replaced by
     Rec(0,v1..vn)..Rec(n-1,v1..vn) respectively.
 *)
type 'a t =
    Var of int * int
  | Node of 'a * 'a t array array
  | Rec of int * 'a t array

(* Building trees *)
let mk_rec_calls i = Array.init i (fun j -> Var(0,j))
let mk_node lab sons = Node (lab, sons)

(* The usual lift operation *)
let rec lift_rtree_rec depth n = function
    Var (i,j) as t -> if i < depth then t else Var (i+n,j)
  | Node (l,sons) -> Node (l,Array.map (Array.map (lift_rtree_rec depth n)) sons)
  | Rec(j,defs) ->
      Rec(j, Array.map (lift_rtree_rec (depth+1) n) defs)

let lift n t = if Int.equal n 0 then t else lift_rtree_rec 0 n t

let rec subst mk sub = function
| Var (i, j) ->
  begin match Esubst.expand_rel (i + 1) sub with
  | Util.Inl (k, v) -> mk k j v
  | Util.Inr (m, _) -> Var (m - 1, j)
  end
| Node (l,sons) -> Node (l,Array.map (Array.map (subst mk sub)) sons)
| Rec(j, defs) ->
  Rec(j, Array.map (subst mk (Esubst.subs_lift sub)) defs)

type 'a clos = Clos of 'a t array * 'a clos Esubst.subs

type 'a expansion = ExpVar of int * int | ExpNode of 'a * 'a clos Esubst.subs * 'a t array array

(* To avoid looping, we must check that every body introduces a node
   or a parameter *)
let rec expand0 sub = function
| Var (i, j) ->
  begin match Esubst.expand_rel (i + 1) sub with
  | Util.Inl (k, v) ->
    let Clos (v, sub) = v in
    expand0 (Esubst.subs_shft (k, sub)) (Rec (j, v))
  | Util.Inr (m, _) -> ExpVar (m - 1, j)
  end
| Rec (j, defs) ->
  let sub = Esubst.subs_cons (Clos (defs, sub)) sub in
  expand0 sub defs.(j)
| Node (l, sons) -> ExpNode (l, sub, sons)

let expand t = match expand0 (Esubst.subs_id 0) t with
| ExpVar (i, j) -> Var (i, j)
| ExpNode (l, sub, sons) ->
  let rec mk k j (Clos (v, sub)) = subst mk (Esubst.subs_shft (k, sub)) (Rec (j, v)) in
  let map t = subst mk sub t in
  let sons = Array.map (fun v -> Array.map map v) sons in
  Node (l, sons)

(* Given a vector of n bodies, builds the n mutual recursive trees.
   Recursive calls are made with parameters (0,0) to (0,n-1). We check
   the bodies actually build something by checking it is not
   directly one of the parameters of depth 0. Some care is taken to
   accept definitions like  rec X=Y and Y=f(X,Y) *)
let mk_rec defs =
  let rec check histo d = match expand d with
  | Var (0, j) ->
    if Int.Set.mem j histo then failwith "invalid rec call"
    else check (Int.Set.add j histo) defs.(j)
  | _ -> ()
  in
  Array.mapi (fun i d -> check (Int.Set.singleton i) d; Rec(i,defs)) defs
(*
let v(i,j) = lift i (mk_rec_calls(j+1)).(j);;
let r = (mk_rec[|(mk_rec[|v(1,0)|]).(0)|]).(0);;
let r = mk_rec[|v(0,1);v(1,0)|];;
the last one should be accepted
*)

(* Tree destructors, expanding loops when necessary *)
let dest_var t = match expand0 (Esubst.subs_id 0) t with
| ExpVar (i, j) -> (i, j)
| _ -> failwith "Rtree.dest_var"

let dest_node t =
  match expand t with
      Node (l,sons) -> (l,sons)
    | _ -> failwith "Rtree.dest_node"

let dest_head t = match expand0 (Esubst.subs_id 0) t with
| ExpVar _ -> failwith "Rtree.dest_head"
| ExpNode (l, _, _) -> l

let is_node t =
  match expand t with
      Node _ -> true
    | _ -> false

let rec map f t = match t with
    Var(i,j) -> Var(i,j)
  | Node (a,sons) -> Node (f a, Array.map (Array.map (map f)) sons)
  | Rec(j,defs) -> Rec (j, Array.map (map f) defs)

module Smart =
struct

  let map f t = match t with
      Var _ -> t
    | Node (a,sons) ->
        let a'=f a and sons' = Array.Smart.map (Array.Smart.map (map f)) sons in
        if a'==a && sons'==sons then t
        else Node (a',sons')
    | Rec(j,defs) ->
        let defs' = Array.Smart.map (map f) defs in
        if defs'==defs then t
        else Rec(j,defs')

end

module Kind =
struct

type 'a rtree = 'a t
type 'a t = { node : 'a rtree; subs : 'a clos Esubst.subs }

let var i j = Var (i, j)
let node l sons = Node (l, sons)

type 'a kind = Var of int * int | Node of 'a * 'a t array array

let make t = { node = t; subs = Esubst.subs_id 0 }

let kind t : 'a kind = match expand0 t.subs t.node with
| ExpVar (i, j) -> Var (i, j)
| ExpNode (l, subs, sons) ->
  let map node = { node; subs } in
  let sons = Array.map (fun v -> Array.map map v) sons in
  Node (l, sons)

let repr t = match expand0 t.subs t.node with
| ExpVar (i, j) -> var i j
| ExpNode (l, subs, sons) ->
  let rec mk k j (Clos (v, sub)) = subst mk (Esubst.subs_shft (k, sub)) (Rec (j, v)) in
  let map t = subst mk subs t in
  let sons = Array.map (fun v -> Array.map map v) sons in
  node l sons

end

(** Structural equality test, parametrized by an equality on elements *)

let rec raw_eq cmp t t' = match t, t' with
  | Var (i,j), Var (i',j') -> Int.equal i i' && Int.equal j j'
  | Node (x, a), Node (x', a') -> cmp x x' && Array.equal (Array.equal (raw_eq cmp)) a a'
  | Rec (i, a), Rec (i', a') -> Int.equal i i' && Array.equal (raw_eq cmp) a a'
  | _ -> false

let raw_eq2 cmp (t,u) (t',u') = raw_eq cmp t t' && raw_eq cmp u u'

(** Equivalence test on expanded trees. It is parametrized by two
    equalities on elements:
    - [cmp] is used when checking for already seen trees
    - [cmp'] is used when comparing node labels. *)

let equiv cmp cmp' =
  let rec compare histo t t' =
    List.mem_f (raw_eq2 cmp) (t,t') histo ||
    match expand t, expand t' with
    | Node(x,v), Node(x',v') ->
        cmp' x x' &&
        Int.equal (Array.length v) (Array.length v') &&
        Array.for_all2 (Array.for_all2 (compare ((t,t')::histo))) v v'
    | _ -> false
  in compare []

(** The main comparison on rtree tries first physical equality, then
    the structural one, then the logical equivalence *)

let equal cmp t t' =
  t == t' || raw_eq cmp t t' || equiv cmp cmp t t'

(** Intersection of rtrees of same arity *)
let rec inter cmp interlbl def n histo t t' =
  try
    let (i,j) = List.assoc_f (raw_eq2 cmp) (t,t') histo in
    Var (n-i-1,j)
  with Not_found ->
  match t, t' with
  | Var (i,j), Var (i',j') ->
      assert (Int.equal i i' && Int.equal j j'); t
  | Node (x, a), Node (x', a') ->
      (match interlbl x x' with
      | None -> mk_node def [||]
      | Some x'' -> Node (x'', Array.map2 (Array.map2 (inter cmp interlbl def n histo)) a a'))
  | Rec (i,v), Rec (i',v') ->
     (* If possible, we preserve the shape of input trees *)
     if Int.equal i i' && Int.equal (Array.length v) (Array.length v') then
       let histo = ((t,t'),(n,i))::histo in
       Rec(i, Array.map2 (inter cmp interlbl def (n+1) histo) v v')
     else
     (* Otherwise, mutually recursive trees are transformed into nested trees *)
       let histo = ((t,t'),(n,0))::histo in
       Rec(0, [|inter cmp interlbl def (n+1) histo (expand t) (expand t')|])
  | Rec _, _ -> inter cmp interlbl def n histo (expand t) t'
  | _ , Rec _ -> inter cmp interlbl def n histo t (expand t')
  | _ -> assert false

let inter cmp interlbl def t t' = inter cmp interlbl def 0 [] t t'

(** Inclusion of rtrees. We may want a more efficient implementation. *)
let incl cmp interlbl def t t' =
  equal cmp t (inter cmp interlbl def t t')

(** Tests if a given tree is infinite, i.e. has a branch of infinite length.
   This corresponds to a cycle when visiting the expanded tree.
   We use a specific comparison to detect already seen trees. *)

let is_infinite cmp t =
  let rec is_inf histo t =
    List.mem_f (raw_eq cmp) t histo ||
    match expand t with
    | Node (_,v) -> Array.exists (Array.exists (is_inf (t::histo))) v
    | _ -> false
  in
  is_inf [] t

(* Pretty-print a tree (not so pretty) *)

let rec pr_tree prl t =
  let open Pp in
  match t with
    | Var (i,j) -> str"#"++int i++str":"++int j
    | Node(lab,[||]) -> prl lab
    | Node(lab,v) ->
        hov 0 (prl lab++str","++spc()++
               str"["++
               hv 0 (prvect_with_sep pr_comma (fun a ->
                   str"("++
                   hv 0 (prvect_with_sep pr_comma (pr_tree prl) a)++
                   str")") v)++
               str"]")
    | Rec(i,v) ->
        if Int.equal (Array.length v) 0 then str"Rec{}"
        else if Int.equal (Array.length v) 1 then
          hv 2 (str"Rec{"++pr_tree prl v.(0)++str"}")
        else
          hv 2 (str"Rec{"++int i++str","++brk(1,0)++
                 prvect_with_sep pr_comma (pr_tree prl) v++str"}")

module Automaton =
struct

type 'a rtree = 'a t

type label = { constructor : int; argpos : int }

module Label =
struct
  type t = label
  let compare p q =
    let c = Int.compare p.constructor q.constructor in
    if Int.equal c 0 then Int.compare p.argpos q.argpos else c
end

module H = Hopcroft.Make(Label)

type state = int

type 'a data = {
  uid : int;
  elt : 'a Int.Map.t;
  trs : state array array Int.Map.t;
}

type 'a t = {
  init : int;
  states : ('a * state array array) array;
}

let initial a = a.init
let data a i = fst a.states.(i)
let transitions a i = snd a.states.(i)
let move a i = { init = i; states = a.states }

let make r =
  let rec aux env state = function
  | Var (i, j) ->
    let vec = Range.get env i in
    state, vec.(j)
  | Node (lbl, args) ->
    let node = state.uid in
    let state = { state with elt = Int.Map.add node lbl state.elt; uid = state.uid + 1 } in
    let fold accu v = Array.fold_left_map (fun accu r -> aux env accu r) accu v in
    let (state, tr) = Array.fold_left_map fold state args in
    let state = { state with trs = Int.Map.add node tr state.trs } in
    state, node
  | Rec (j, v) ->
    let map = function
    | Var _ | Rec _ ->
      assert false (* does not happen for rtrees generated from an inductive *)
    | Node (lbl, args) -> (lbl, args)
    in
    let uid = state.uid in
    let v = Array.map map v in
    let self = Array.mapi (fun i _ -> state.uid + i) v in
    let nelt = Array.fold_left_i (fun i accu (lbl, _) -> Int.Map.add (state.uid + i) lbl accu) state.elt v in
    let state = { state with elt = nelt; uid = state.uid + Array.length v } in
    let env = Range.cons self env in
    let fold pos accu (_lbl, args) =
      let fold accu v = Array.fold_left_map (fun accu r -> aux env accu r) accu v in
      let (accu, tr) = Array.fold_left_map fold accu args in
      { accu with trs = Int.Map.add (uid + pos) tr accu.trs }
    in
    let state = Array.fold_left_i fold state v in
    state, self.(j)
  in
  let state, init = aux Range.empty { uid = 0; trs = Int.Map.empty; elt = Int.Map.empty } r in
  let states = Array.init state.uid (fun i -> Int.Map.find i state.elt, Int.Map.find i state.trs) in
  { init; states }

let compact (type data) (cmp : data -> data -> int) { init; states } =
  let module Data = struct type t = data let compare = cmp end in
  let module LMap = Map.Make(Data) in
  let fold i accu (label, _) = match LMap.find_opt label accu with
  | None -> LMap.add label [i] accu
  | Some l -> LMap.add label (i :: l) accu
  in
  let partitions = Array.fold_left_i fold LMap.empty states in
  let partitions = List.map snd @@ LMap.bindings partitions in
  let fold src accu (_, trs) =
    let fold i accu v =
      let fold j accu dst = { H.src = src; H.lbl = { constructor = i; argpos = j }; H.dst = dst } :: accu in
      Array.fold_left_i fold accu v
    in
    Array.fold_left_i fold accu trs
  in
  let transitions = Array.fold_left_i fold [] states in
  let classes =
    if List.is_empty transitions then
      Array.of_list partitions
    else
      let automaton = {
        H.states = Array.length states;
        H.partitions = partitions;
        H.transitions = transitions;
      } in
      H.reduce automaton
  in
  (* Canonicalize transitions *)
  let fold i accu l = List.fold_left (fun accu orig -> Int.Map.add orig i accu) accu l in
  let map = Array.fold_left_i fold Int.Map.empty classes in
  let canon st =
    let can = match st with
    | [] -> assert false
    | can :: _ -> can
    in
    let v, tr = states.(can) in
    let ntr = Array.map (fun v -> Array.map (fun dst -> Int.Map.get dst map) v) tr in
    v, ntr
  in
  let nstates = Array.map canon classes in
  let ninit = Int.Map.find init map in
  { init = ninit; states = nstates }

module IntPair = OrderedType.Pair(Int)(Int)
module IntPairMap = Map.Make(IntPair)

let merge_array f v1 v2 =
  let len1 = Array.length v1 in
  let len2 = Array.length v2 in
  let len = if len1 < len2 then len1 else len2 in
  Array.init len (fun i -> f v1.(i) v2.(i))

let inter f a1 a2=
  let { init = i1; states = st1 } = a1 in
  let { init = i2; states = st2 } = a2 in
  if Int.equal i1 i2 && st1 == st2 then a1
  else
    let rec search seen i1 i2 =
      if IntPairMap.mem (i1, i2) seen then seen
      else
        let (v1, tr1) = st1.(i1) in
        let (v2, tr2) = st2.(i2) in
        let v = f v1 v2 in
        let merge v1 v2 = merge_array (fun t1 t2 -> t1, t2) v1 v2 in
        let tr = merge_array merge tr1 tr2 in
        let seen = IntPairMap.add (i1, i2) (v, tr) seen in
        let fold seen v =
          let fold seen (tgt1, tgt2) = search seen tgt1 tgt2 in
          Array.fold_left fold seen v
        in
        Array.fold_left fold seen tr
    in
    let seen = search IntPairMap.empty i1 i2 in
    let fold p _ (i, dir, rev) = (i + 1, IntPairMap.add p i dir, Int.Map.add i p rev) in
    let (_, dir, rev) = IntPairMap.fold fold seen (0, IntPairMap.empty, Int.Map.empty) in
    let len = IntPairMap.cardinal dir in
    let mk i =
      let p = Int.Map.find i rev in
      let (v, tr) = IntPairMap.find p seen in
      let ntr = Array.map (fun v -> Array.map (fun p -> IntPairMap.find p dir) v) tr in
      (v, ntr)
    in
    let nstates = Array.init len mk in
    let ninit = IntPairMap.get (i1, i2) dir in
    { init = ninit; states = nstates }

exception Different

let check_len v1 v2 =
  if not (Int.equal (Array.length v1) (Array.length v2)) then raise Different

(* The function below expects the automata to be minimal *)
let equal eqf { init = i1; states = st1 } { init = i2; states = st2 } =
  let rec search seen1 seen2 equiv i1 i2 =
    if IntPairMap.mem (i1, i2) equiv then (seen1, seen2, equiv)
    else if Int.Set.mem i1 seen1 || Int.Set.mem i2 seen2 then raise Different
    else
      let (v1, tr1) = st1.(i1) in
      let (v2, tr2) = st2.(i2) in
      let () = if not (eqf v1 v2) then raise Different in
      let seen1 = Int.Set.add i1 seen1 in
      let seen2 = Int.Set.add i2 seen2 in
      let equiv = IntPairMap.add (i1, i2) () equiv in
      let () = check_len tr1 tr2 in
      let fold accu v1 v2 =
        let () = check_len v1 v2 in
        Array.fold_left2 (fun (seen1, seen2, equiv) tgt1 tgt2 -> search seen1 seen2 equiv tgt1 tgt2) accu v1 v2
      in
      Array.fold_left2 fold (seen1, seen2, equiv) tr1 tr2
  in
  (Int.equal i1 i2 && st1 == st2) ||
  match search Int.Set.empty Int.Set.empty IntPairMap.empty i1 i2 with
  | _ -> true
  | exception Different -> false

let map f { init; states } =
  let map (v, tr) = f v, tr in
  let states = Array.map map states in
  { init; states }

end
