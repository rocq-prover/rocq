(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Names
open Constr
open Context
open Univ
open Environ
open EConstr
open Vars
open Context.Rel.Declaration

(** This module implements a call by name reduction used by the cbn tactic.

    It has an ability to "refold" constants by storing constants and
    their parameters in its stack.
*)

(** Machinery to custom the behavior of the reduction *)
module ReductionBehaviour = Reductionops.ReductionBehaviour

type cst_info = { volatile : bool; alias : bool; refold_after_iota : bool }

(** Machinery about stack of unfolded constants *)
module Cst_stack = struct
  open EConstr

(** constant * params * args

- constant applied to params = term in head applied to args
- there is at most one arguments with an empty list of args, it must be the first.
- in args, the int represents the indice of the first arg to consider *)
  type 'a t = (constr * 'a list * (int * 'a array) list * cst_info)  list

  let empty = []
  let all_volatile l = CList.for_all (fun (_,_,_,{volatile; _}) -> volatile) l
  let may_refold_alias_after_iota = function
    | (_,_,_,{alias=true; refold_after_iota=true; _}) :: _ -> true
    | [] | (_,_,_,{alias=false; _}) :: _
    | (_,_,_,{alias=true; refold_after_iota=false; _}) :: _ -> false
  let mark_alias ?(refold_after_iota=false) = function
    | (c, params, args, info) :: l ->
      (c, params, args,
       { info with alias = true; refold_after_iota = info.refold_after_iota || refold_after_iota }) :: l
    | [] -> []

  let drop_useless = function
    | _ :: ((_,_,[],_)::_ as q) -> q
    | l -> l

  let add_param h cst_l =
    let append2cst = function
      | (c,params,[],vol) -> (c, h::params, [], vol)
      | (c,params,((i,t)::q),vol) when i = pred (Array.length t) ->
        (c, params, q, vol)
      | (c,params,(i,t)::q, vol) ->
        (c, params, (succ i,t)::q, vol)
    in
      drop_useless (List.map append2cst cst_l)

  let add_args cl =
    List.map (fun (a,b,args,vol) -> (a,b,(0,cl)::args,vol))

  let add_cst ?(volatile=false) ?(refold_after_iota=false) cst = function
    | (_,_,[],_) :: q as l -> l
    | l -> (cst,[],[],{volatile; alias=false; refold_after_iota})::l

  let best_cst = function
    | (cst,params,[],_)::_ -> Some(cst,params)
    | _ -> None

  let reference sigma force t = match best_cst t with
    | Some (c, params) when isConst sigma c -> Some (fst (destConst sigma c), List.map force params)
    | _ -> None

  (** [best_replace d cst_l c] makes the best replacement for [d]
      by [cst_l] in [c] *)
  let best_replace sigma force d cst_l c =
    let reconstruct_head = List.fold_left
      (fun t (i,args) ->
         let args = Array.map force (Array.sub args i (Array.length args - i)) in
         mkApp (t,args)) in
    List.fold_right
      (fun (cst,params,args,_) t -> Termops.replace_term sigma
        (reconstruct_head d args)
        (applist (cst, List.rev_map force params))
        t) cst_l c

  let pr env sigma pr_a l =
    let open Pp in
    let p_c c = Termops.Internal.print_constr_env env sigma c in
    prlist_with_sep pr_semicolon
      (fun (c,params,args,{volatile; alias; refold_after_iota}) ->
        hov 1 (str"(" ++ p_c c ++ str ")" ++ spc () ++ pr_sequence pr_a params ++ spc () ++ str "(args:" ++
                 pr_sequence (fun (i,el) -> prvect_with_sep spc pr_a (Array.sub el i (Array.length el - i))) args ++
               str ")" ++
              (if volatile then str " (volatile)" else mt()) ++
              (if alias then str " (alias)" else mt()) ++
              (if refold_after_iota then str " (refold-after-iota)" else mt()))) l
end

module CbnClos = struct
  open EConstr

  (* [force] is deliberately cached for non-identity substitutions: several
     refolding/progress checks compare the same delayed closure repeatedly. *)
  type t = { term : constr; subst : t Esubst.subs; mutable forced : constr option }

  type array_view = {
    array_length : int;
    array_get : int -> t;
    array_default : t;
  }

  type view =
    | NotArray of (t, t, ESorts.t, EInstance.t, ERelevance.t) Constr.kind_of_term
    | Array of array_view

  let notarray x = NotArray x

  let id_subst = Esubst.subs_id 0
  let inject term = { term; subst = id_subst; forced = None }
  let mk_clos subst term =
    if Esubst.is_subs_id subst then inject term else { term; subst; forced = None }
  let mk_clos_vect subst v = Array.map (mk_clos subst) v
  let lift n c =
    if Int.equal n 0 then c else { term = c.term; subst = Esubst.subs_shft (n, c.subst); forced = None }
  let liftn n c =
    if Int.equal n 0 then c else { term = c.term; subst = Esubst.subs_liftn n c.subst; forced = None }
  let is_id_subst c = Esubst.is_subs_id c.subst
  let subst_cons v c = mk_clos (Esubst.subs_cons v c.subst) c.term

  (* Closure-level application used by internal continuations that need to keep
     constructor/constant spines without forcing all arguments. *)
  let mk_app f args =
    match args with
    | [] -> f
    | _ :: _ ->
      let nargs = List.length args in
      let term = mkApp (mkRel 1, Array.init nargs (fun i -> mkRel (i + 2))) in
      let subst = List.fold_right Esubst.subs_cons (f :: args) id_subst in
      mk_clos subst term

  let mk_array u elems def ty =
    let n = Array.length elems in
    let term = mkArray (u, Array.init n (fun i -> mkRel (i + 1)), mkRel (n + 1), mkRel (n + 2)) in
    let subst = List.fold_right Esubst.subs_cons (Array.to_list elems @ [def; ty]) id_subst in
    mk_clos subst term

  let rec force sigma c =
    if Esubst.is_subs_id c.subst then c.term
    else match c.forced with
    | Some t -> t
    | None ->
      let t = EConstr.Vars.esubst (fun k v -> force sigma (lift k v)) c.subst c.term in
      c.forced <- Some t;
      t

  let force_vect sigma v = Array.map (force sigma) v
  let force_under sigma n c = force sigma (liftn n c)
  let force_under_vect sigma n v = Array.map (force_under sigma n) v

  let force_invert sigma = function
    | NoInvert -> NoInvert
    | CaseInvert { indices } -> CaseInvert { indices = force_vect sigma indices }

  let force_return sigma ((nas, p), r) =
    ((nas, force_under sigma (Array.length nas) p), r)

  let force_branch sigma (nas, b) =
    (nas, force_under sigma (Array.length nas) b)

  let force_branches sigma brs = Array.map (force_branch sigma) brs

  let force_fix sigma ((ri, n), (names, types, bodies)) =
    let nb = Array.length bodies in
    ((ri, n), (names, force_vect sigma types, force_under_vect sigma nb bodies))

  let force_cofix sigma (n, (names, types, bodies)) =
    let nb = Array.length bodies in
    (n, (names, force_vect sigma types, force_under_vect sigma nb bodies))

  let map_invert subst = function
    | NoInvert -> NoInvert
    | CaseInvert { indices } -> CaseInvert { indices = mk_clos_vect subst indices }

  (* If [c] is syntactically a substituted de Bruijn variable, return the
     substituted value without weak-head reducing that value.  This is used to
     recognize wrappers such as [fun x => x] without speculatively reducing
     their arguments. *)
  let rec subst_value sigma c =
    match EConstr.kind sigma c.term with
    | Rel n ->
      begin match Esubst.expand_rel n c.subst with
      | Inl (k, v) -> Some (lift k v)
      | Inr _ -> None
      end
    | Cast (b, _, _) -> subst_value sigma (mk_clos c.subst b)
    | _ -> None

  let equal sigma a b =
    a == b || (a.term == b.term && a.subst == b.subst) ||
    (* TODO: add fast path that returns false on non-Rel terms whose head is not of the same shape.
       Alternatively, fuse the equality check and the substitution *)
    let a = force sigma a in
    let b = force sigma b in
    a == b || EConstr.eq_constr sigma a b

  let equal_under sigma n a b = equal sigma (liftn n a) (liftn n b)

  let rec kind sigma c : view =
    match EConstr.kind sigma c.term with
    | Rel n ->
      begin match Esubst.expand_rel n c.subst with
      | Inl (k, v) -> kind sigma (lift k v)
      | Inr (k, _) -> notarray @@ Rel k
      end
    | Var id -> notarray @@ Var id
    | Meta mv -> notarray @@ Meta mv
    | Evar (ev, args) -> notarray @@ Evar (ev, SList.Skip.map (mk_clos c.subst) args)
    | Sort s -> notarray @@ Sort s
    | Cast (b, k, t) -> notarray @@ Cast (mk_clos c.subst b, k, mk_clos c.subst t)
    | Prod (na, t, b) -> notarray @@ Prod (na, mk_clos c.subst t, mk_clos c.subst b)
    | Lambda (na, t, b) -> notarray @@ Lambda (na, mk_clos c.subst t, mk_clos c.subst b)
    | LetIn (na, b, t, c') -> notarray @@ LetIn (na, mk_clos c.subst b, mk_clos c.subst t, mk_clos c.subst c')
    | App (f, args) -> notarray @@ App (mk_clos c.subst f, mk_clos_vect c.subst args)
    | Const cst -> notarray @@ Const cst
    | Ind ind -> notarray @@ Ind ind
    | Construct cstr -> notarray @@ Construct cstr
    | Case (ci, u, pms, ((nas, p), r), iv, d, brs) ->
      let p = ((nas, mk_clos c.subst p), r) in
      let brs = Array.map (fun (nas, b) -> (nas, mk_clos c.subst b)) brs in
      notarray @@ Case (ci, u, mk_clos_vect c.subst pms, p, map_invert c.subst iv, mk_clos c.subst d, brs)
    | Fix ((ri, n), (names, types, bodies)) ->
      notarray @@ Fix ((ri, n), (names, mk_clos_vect c.subst types, mk_clos_vect c.subst bodies))
    | CoFix (n, (names, types, bodies)) ->
      notarray @@ CoFix (n, (names, mk_clos_vect c.subst types, mk_clos_vect c.subst bodies))
    | Proj (p, r, c') -> notarray @@ Proj (p, r, mk_clos c.subst c')
    | Int _ | Float _ | String _ as k -> notarray k
    | Array (u, elems, def, ty) ->
      let subst = c.subst in
      Array {
        array_length = Array.length elems;
        array_get = (fun i -> mk_clos subst elems.(i));
        array_default = mk_clos subst def;
      }

  let array_view sigma c =
    match kind sigma c with
    | Array v -> Some v
    | NotArray _ -> None

end


(** The type of (machine) stacks (= lambda-bar-calculus' contexts) *)
module Stack :
sig
  open EConstr
  type 'a app_node

  type cst_member =
    | Cst_const of pconstant
    | Cst_proj of Projection.t * ERelevance.t

  type 'a case_stk =
    case_info * EInstance.t * 'a array * ('a,ERelevance.t) pcase_return * 'a pcase_invert * ('a,ERelevance.t) pcase_branch array
  type 'a member =
  | App of 'a app_node
  | Case of 'a case_stk * 'a Cst_stack.t
  | Proj of Projection.t * ERelevance.t * 'a Cst_stack.t
  | Fix of ('a, 'a, ERelevance.t) pfixpoint * 'a t * 'a Cst_stack.t
  | Primitive of CPrimitives.t * (Constant.t * EInstance.t) * 'a t * CPrimitives.args_red * 'a Cst_stack.t
  | Cst of { const : cst_member;
             curr : int;
             remains : int list;
             params : 'a t;
             volatile : bool;
             refold_after_iota : bool;
             cst_l : 'a Cst_stack.t;
           }

  and 'a t = 'a member list

  val pr : ('a -> Pp.t) -> 'a t -> Pp.t
  val empty : 'a t
  val append_app : 'a array -> 'a t -> 'a t
  val decomp : 'a t -> ('a * 'a t) option
  val equal : env -> ('a -> 'a -> bool) -> (('a, 'a, ERelevance.t) pfixpoint -> ('a, 'a, ERelevance.t) pfixpoint -> bool)
    -> ('a case_stk -> 'a case_stk -> bool) -> 'a t -> 'a t -> bool
  val strip_app : 'a t -> 'a t * 'a t
  val strip_n_app : int -> 'a t -> ('a t * 'a * 'a t) option
  val will_expose_iota : 'a t -> bool
  val list_of_app_stack : 'a t -> 'a list option
  val app_stack_for_all : ('a -> bool) -> 'a t -> bool
  val args_size : 'a t -> int
  val tail : int -> 'a t -> 'a t
  val nth : 'a t -> int -> 'a
  val best_state : inject:(constr -> 'a) -> equal:('a -> 'a -> bool) -> 'a * 'a t -> 'a Cst_stack.t -> 'a * 'a t
  val zip : ?refold:bool -> Evd.evar_map ->
    force:('a -> constr) ->
    force_return:(('a,ERelevance.t) pcase_return -> (constr,ERelevance.t) pcase_return) ->
    force_invert:('a pcase_invert -> constr pcase_invert) ->
    force_branch:(('a,ERelevance.t) pcase_branch -> (constr,ERelevance.t) pcase_branch) ->
    force_fix:(('a, 'a, ERelevance.t) pfixpoint -> (constr, constr, ERelevance.t) pfixpoint) ->
    inject:(constr -> 'a) -> equal:('a -> 'a -> bool) -> 'a * 'a t -> constr
  val check_native_args : CPrimitives.t -> 'a t -> bool
  val get_next_primitive_args : CPrimitives.args_red -> 'a t -> CPrimitives.args_red * ('a t * 'a * 'a t) option
end =
struct
  open EConstr
  type 'a app_node = int * 'a array * int
  (* first releavnt position, arguments, last relevant position *)

  (*
     Invariant that this module must ensure:
     - in app_node (i,_,j) i <= j
     - There is no array reallocation (outside of debug printing)
   *)

  let pr_app_node pr (i,a,j) =
    let open Pp in surround (
                     prvect_with_sep pr_comma pr (Array.sub a i (j - i + 1))
                     )


  type cst_member =
    | Cst_const of pconstant
    | Cst_proj of Projection.t * ERelevance.t

  type 'a case_stk =
    case_info * EInstance.t * 'a array * ('a,ERelevance.t) pcase_return * 'a pcase_invert * ('a,ERelevance.t) pcase_branch array
  type 'a member =
  | App of 'a app_node
  | Case of 'a case_stk * 'a Cst_stack.t
  | Proj of Projection.t * ERelevance.t * 'a Cst_stack.t
  | Fix of ('a, 'a, ERelevance.t) pfixpoint * 'a t * 'a Cst_stack.t
  | Primitive of CPrimitives.t * (Constant.t * EInstance.t) * 'a t * CPrimitives.args_red * 'a Cst_stack.t
  | Cst of { const : cst_member;
             curr : int;
             remains : int list;
             params : 'a t;
             volatile : bool;
             refold_after_iota : bool;
             cst_l : 'a Cst_stack.t;
           }

  and 'a t = 'a member list

  (* Debugging printer *)
  let rec pr_member pr_c member =
    let open Pp in
    let pr_c x = hov 1 (pr_c x) in
    match member with
    | App app -> str "ZApp" ++ pr_app_node pr_c app
    | Case ((_,_,_,_,_,br),cst) ->
       str "ZCase(" ++
         prvect_with_sep (pr_bar) (fun (_, b) -> pr_c b) br
       ++ str ")"
    | Proj (p,_,cst) ->
      str "ZProj(" ++ Projection.debug_print p ++ str ")"
    | Fix (f,args,cst) ->
       str "ZFix(" ++ Constr.debug_print_fix pr_c f
       ++ pr_comma () ++ pr pr_c args ++ str ")"
    | Primitive (p,c,args,kargs,cst_l) ->
      str "ZPrimitive(" ++ str (CPrimitives.to_string p)
      ++ pr_comma () ++ pr pr_c args ++ str ")"
    | Cst {const=mem;curr;remains;params;cst_l;refold_after_iota} ->
      str "ZCst(" ++ pr_cst_member pr_c mem ++ pr_comma () ++ int curr
      ++ pr_comma () ++
        prlist_with_sep pr_semicolon int remains ++
        pr_comma () ++ pr pr_c params ++
        (if refold_after_iota then str ", refold-after-iota" else mt()) ++ str ")"
  and pr pr_c l =
    let open Pp in
    prlist_with_sep pr_semicolon (fun x -> hov 1 (pr_member pr_c x)) l

  and pr_cst_member pr_c c =
    let open Pp in
      match c with
      | Cst_const (c, u) ->
        if UVars.Instance.is_empty u then Constant.debug_print c
        else str"(" ++ Constant.debug_print c ++ str ", " ++
          UVars.Instance.pr Sorts.raw_printer u ++ str")"
      | Cst_proj (p,r) ->
        str".(" ++ Projection.debug_print p ++ str")"

  let empty = []

  let append_app v s =
    let le = Array.length v in
    if Int.equal le 0 then s else App (0,v,pred le) :: s

  let decomp_node (i,l,j) sk =
    if i < j then (l.(i), App (succ i,l,j) :: sk)
    else (l.(i), sk)

  let decomp = function
    | App node::s -> Some (decomp_node node s)
    | _ -> None

  let decomp_node_last (i,l,j) sk =
    if i < j then (l.(j), App (i,l,pred j) :: sk)
    else (l.(j), sk)

  let equal env f f_fix f_case sk1 sk2 =
    let equal_cst_member x y =
      match x, y with
      | Cst_const (c1,u1), Cst_const (c2, u2) ->
        QConstant.equal env c1 c2 && UVars.Instance.equal u1 u2
      | Cst_proj (p1,_), Cst_proj (p2,_) -> QProjection.Repr.equal env (Projection.repr p1) (Projection.repr p2)
      | _, _ -> false
    in
    let rec equal_rec sk1 sk2 =
      match sk1,sk2 with
      | [],[] -> true
      | App a1 :: s1, App a2 :: s2 ->
        let t1,s1' = decomp_node_last a1 s1 in
        let t2,s2' = decomp_node_last a2 s2 in
        (f t1 t2) && (equal_rec s1' s2')
      | Case ((ci1,pms1,p1,t1,iv1,a1),_) :: s1, Case ((ci2,pms2,p2,iv2,t2,a2),_) :: s2 ->
        f_case (ci1,pms1,p1,t1,iv1,a1) (ci2,pms2,p2,iv2,t2,a2) && equal_rec s1 s2
      | (Proj (p,_,_)::s1, Proj(p2,_,_)::s2) ->
        QProjection.Repr.equal env (Projection.repr p) (Projection.repr p2)
        && equal_rec s1 s2
      | Fix (f1,s1,_) :: s1', Fix (f2,s2,_) :: s2' ->
        f_fix f1 f2
          && equal_rec (List.rev s1) (List.rev s2)
          && equal_rec s1' s2'
      | Cst c1::s1', Cst c2::s2' ->
        equal_cst_member c1.const c2.const
          && equal_rec (List.rev c1.params) (List.rev c2.params)
          && equal_rec s1' s2'
      | ((App _|Case _|Proj _|Fix _|Cst _|Primitive _)::_|[]), _ -> false
    in equal_rec (List.rev sk1) (List.rev sk2)

  let append_app_list l s =
    let a = Array.of_list l in
    append_app a s

  let rec args_size = function
    | App (i,_,j)::s -> j + 1 - i + args_size s
    | (Case _|Fix _|Proj _|Cst _|Primitive _)::_ | [] -> 0

  let strip_app s =
    let rec aux out = function
      | ( App _ as e) :: s -> aux (e :: out) s
      | s -> List.rev out,s
    in aux [] s
  let strip_n_app n s =
    let rec aux n out = function
      | App (i,a,j) as e :: s ->
         let nb = j  - i + 1 in
         if n >= nb then
           aux (n - nb) (e::out) s
         else
           let p = i+n in
           Some (CList.rev
              (if Int.equal n 0 then out else App (i,a,p-1) :: out),
            a.(p),
            if j > p then App(succ p,a,j)::s else s)
      | s -> None
    in aux n [] s

  let will_expose_iota args =
    List.exists
      (function (Fix (_,_,l) | Case (_,l) |
                 Proj (_,_,l) | Cst {cst_l=l}) when Cst_stack.all_volatile l -> true | _ -> false)
      args

  let list_of_app_stack s =
    let rec aux = function
      | App (i,a,j) :: s ->
        let (args',s') = aux s in
        let a' = Array.sub a i (j - i + 1) in
        (Array.fold_right (fun x y -> x::y) a' args', s')
      | s -> ([],s) in
    let (out,s') = aux s in
    let init = match s' with [] -> true | _ -> false in
    Option.init init out

  let app_stack_for_all p s =
    let rec aux = function
      | App (i,a,j) :: s ->
        let rec loop k = k > j || (p a.(k) && loop (succ k)) in
        loop i && aux s
      | [] -> true
      | _ :: _ -> false
    in aux s

  let tail n0 s0 =
    let rec aux n s =
      if Int.equal n 0 then s else
        match s with
      | App (i,a,j) :: s ->
         let nb = j  - i + 1 in
         if n >= nb then
           aux (n - nb) s
         else
           let p = i+n in
           if j >= p then App(p,a,j)::s else s
        | _ -> raise (Invalid_argument "Reductionops.Stack.tail")
    in aux n0 s0

  let nth s p =
    match strip_n_app p s with
    | Some (_,el,_) -> el
    | None -> raise Not_found

  (** This function breaks the abstraction of Cst_stack ! *)
  let best_state_opt ~inject ~equal sk l =
    let rec aux sk def = function
      |(_,_,_,{volatile=true; _}) -> def
      |(cst, params, [], _) -> Some (inject cst, append_app_list (List.rev params) sk)
      |(cst, params, (i,t)::q, vol) -> match decomp sk with
        | Some (el,sk') when equal el t.(i) ->
          if i = pred (Array.length t)
          then aux sk' def (cst, params, q, vol)
          else aux sk' def (cst, params, (succ i,t)::q, vol)
        | _ -> def
    in List.fold_left (aux sk) None l

  let best_state ~inject ~equal (_,sk as s) l =
    match best_state_opt ~inject ~equal sk l with
    | Some s -> s
    | None -> s

  let constr_of_cst_member force inject f sk =
    match f with
    | Cst_const (c, u) -> inject (mkConstU (c, EInstance.make u)), sk
    | Cst_proj (p,r) ->
      match decomp sk with
      | Some (hd, sk) -> inject (mkProj (p, r, force hd)), sk
      | None -> assert false

  let zip ?(refold=false) sigma ~force ~force_return ~force_invert ~force_branch ~force_fix ~inject ~equal s =
  (* [best_state_opt] only inspects the residual stack.  Try it before
     materializing eliminated terms: on success the reconstructed case/fix/proj
     would be discarded immediately. *)
  let best_refold = best_state_opt ~inject ~equal in
  let rec zip = function
    | f, [] -> force f
    | f, (App (i,a,j) :: s) ->
       let a' = if Int.equal i 0 && Int.equal j (Array.length a - 1)
                then a
                else Array.sub a i (j - i + 1) in
       zip (inject (mkApp (force f, Array.map force a')), s)
    | f, (Case ((ci,u,pms,rt,iv,br),cst_l)::s) when refold ->
      begin match best_refold s cst_l with
      | Some state -> zip state
      | None ->
        let case = mkCase (ci,u,Array.map force pms,force_return rt,force_invert iv,force f,Array.map force_branch br) in
        zip (inject case, s)
      end
    | f, (Case ((ci,u,pms,rt,iv,br),_)::s) ->
      zip (inject (mkCase (ci,u,Array.map force pms,force_return rt,force_invert iv,force f,Array.map force_branch br)), s)
    | f, (Fix (fix,st,cst_l)::s) when refold ->
      let sk = st @ append_app [|f|] s in
      begin match best_refold sk cst_l with
      | Some state -> zip state
      | None -> zip (inject (mkFix (force_fix fix)), sk)
      end
  | f, (Fix (fix,st,_)::s) -> zip
    (inject (mkFix (force_fix fix)), st @ (append_app [|f|] s))
  | f, (Cst {const;params;cst_l}::s) when refold ->
    let sk = params @ append_app [|f|] s in
    begin match const with
    | Cst_const (c, u) ->
      begin match best_refold sk cst_l with
      | Some state -> zip state
      | None -> zip (inject (mkConstU (c, EInstance.make u)), sk)
      end
    | Cst_proj (p, r) ->
      match decomp sk with
      | Some (hd, sk) ->
        begin match best_refold sk cst_l with
        | Some state -> zip state
        | None -> zip (inject (mkProj (p, r, force hd)), sk)
        end
      | None -> assert false
    end
  | f, (Cst {const;params}::s) ->
    zip (constr_of_cst_member force inject const (params @ (append_app [|f|] s)))
  | f, (Proj (p,r,cst_l)::s) when refold ->
    begin match best_refold s cst_l with
    | Some state -> zip state
    | None -> zip (inject (mkProj (p,r,force f)),s)
    end
  | f, (Proj (p,r,_)::s) -> zip (inject (mkProj (p,r,force f)),s)
  | f, (Primitive (p,c,args,kargs,cst_l)::s) ->
      zip (inject (mkConstU c), args @ append_app [|f|] s)
  in
  zip s

  (* Check if there is enough arguments on [stk] w.r.t. arity of [op] *)
  let check_native_args op stk =
    let nargs = CPrimitives.arity op in
    let rargs = args_size stk in
    nargs <= rargs

  let get_next_primitive_args kargs stk =
    let rec nargs = function
      | [] -> 0
      | CPrimitives.Kwhnf :: _ -> 0
      | _ :: s -> 1 + nargs s
    in
    let n = nargs kargs in
    (List.skipn (n+1) kargs, strip_n_app n stk)

end

(** The type of (machine) states (= lambda-bar-calculus' cuts) *)

(*************************************)
(*** Reduction Functions Operators ***)
(*************************************)

(*************************************)
(*** Reduction using bindingss ***)
(*************************************)

(* Beta Reduction tools *)

let stack_zip ?refold sigma =
  Stack.zip ?refold sigma
    ~force:(CbnClos.force sigma)
    ~force_return:(CbnClos.force_return sigma)
    ~force_invert:(CbnClos.force_invert sigma)
    ~force_branch:(CbnClos.force_branch sigma)
    ~force_fix:(CbnClos.force_fix sigma)
    ~inject:CbnClos.inject
    ~equal:(CbnClos.equal sigma)

let clos_of_app_stack sigma x args =
  if CbnClos.is_id_subst x && Stack.app_stack_for_all CbnClos.is_id_subst args then
    CbnClos.inject (stack_zip sigma (x,args))
  else match Stack.list_of_app_stack args with
  | Some args -> CbnClos.mk_app x args
  | None -> assert false

let reduce_array_primitive sigma u p args =
  let get i = Array.get args i in
  let get_int i = match CbnClos.kind sigma (get i) with
    | NotArray Int i -> Some i
    | _ -> None
  in
  let get_array i = CbnClos.array_view sigma (get i) in
  let bounded_index len i =
    if Uint63.le Uint63.zero i && Uint63.lt i (Uint63.of_int len)
    then Some (snd (Uint63.to_int2 i))
    else None
  in
  let elems_of_array a = Array.init a.CbnClos.array_length a.CbnClos.array_get in
  let mk_array elems def ty = CbnClos.mk_array u elems def ty in
  try match p with
  | CPrimitives.Arraymake ->
    begin match get_int 1 with
    | Some len ->
      let a = Parray.make len (get 2) in
      let elems, def = Parray.to_array a in
      Some (mk_array elems def (get 0))
    | None -> None
    end
  | CPrimitives.Arrayget ->
    begin match get_array 1, get_int 2 with
    | Some a, Some i ->
      let elt = match bounded_index a.CbnClos.array_length i with
        | Some i -> a.CbnClos.array_get i
        | None -> a.CbnClos.array_default
      in
      Some elt
    | _, _ -> None
    end
  | CPrimitives.Arraydefault ->
    begin match get_array 1 with
    | Some a -> Some a.CbnClos.array_default
    | None -> None
    end
  | CPrimitives.Arrayset ->
    begin match get_array 1, get_int 2 with
    | Some a, Some i ->
      let elems = match bounded_index a.CbnClos.array_length i with
        | Some i -> Array.init a.CbnClos.array_length (fun j -> if Int.equal i j then get 3 else a.CbnClos.array_get j)
        | None -> elems_of_array a
      in
      Some (mk_array elems a.CbnClos.array_default (get 0))
    | _, _ -> None
    end
  | CPrimitives.Arraycopy ->
    begin match get_array 1 with
    | Some a -> Some (mk_array (elems_of_array a) a.CbnClos.array_default (get 0))
    | None -> None
    end
  | CPrimitives.Arraylength ->
    begin match get_array 1 with
    | Some a -> Some (CbnClos.inject (mkInt (Uint63.of_int a.CbnClos.array_length)))
    | None -> None
    end
  | _ -> None
  with Invalid_argument _ -> None

let apply_subst sigma cst_l t stack =
  let rec aux cst_l t stack =
    match (Stack.decomp stack, CbnClos.kind sigma t) with
    | Some (h,stacktl), NotArray Lambda (_,_,c) ->
       let cst_l' = Cst_stack.add_param h cst_l in
       aux cst_l' (CbnClos.subst_cons h c) stacktl
    | _ ->
      let cst_l = match CbnClos.subst_value sigma t with
        | Some tm ->
          let refold_after_iota = match stack, CbnClos.kind sigma tm with
            | _ :: _, NotArray (Const _ | Var _ | Rel _) -> true
            | [], _ | _ :: _, _ -> false
          in
          Cst_stack.mark_alias ~refold_after_iota cst_l
        | None -> cst_l
      in
      (cst_l, (t, stack))
  in
  aux cst_l t stack

(* Iota reduction tools *)

(** @return c if there is a constant c whose body is bd
    @return bd else.

    It has only a meaning because internal representation of "Fixpoint f x
    := t" is Definition f := fix f x => t

    Even more fragile that we could hope because do Module M. Fixpoint
    f x := t. End M. Definition f := u. and say goodbye to any hope
    of refolding M.f this way ...
*)
let magically_constant_of_fixbody env sigma (reference, params) bd = function
  | Name.Anonymous -> bd
  | Name.Name id ->
    let open UnivProblem in
    let cst = Constant.change_label reference id in
    if not (Environ.mem_constant cst env) then bd
    else
      let (cst, u), ctx = UnivGen.fresh_constant_instance env cst in
      match constant_opt_value_in env (cst,u) with
      | None -> bd
      | Some t ->
        let csts = EConstr.eq_constr_universes env sigma (Reductionops.beta_applist sigma (EConstr.of_constr t, params)) bd in
        begin match csts with
          | Some csts ->
            let addqs l r (qs,us) = Sorts.QVar.Map.add l r qs, us in
            let addus l r (qs,us) = qs, Univ.Level.Map.add l r us in
            let subst = Set.fold (fun cst acc ->
                match cst with
                | QLeq _ | QElimTo _ -> assert false (* eq_constr_universes cannot produce QLeq nor QElimTo constraints *)
                | QEq (a, b) ->
                  let a = match a with
                    | QVar q -> q
                    | _ -> assert false
                  in
                  addqs a b acc
                  | ULub (u, v) | UWeak (u, v) -> addus u v acc
                  | UEq (u, v) | ULe (u, v) ->
                    (* XXX add something when qsort? *)
                    let get u = match u with
                    | Sorts.SProp | Sorts.Prop -> assert false
                    | Sorts.Set -> Level.set
                    | Sorts.Type u | Sorts.GSort (_, u)
                    | Sorts.VSort (_, u) -> Option.get (Universe.level u)
                    in
                    addus (get u) (get v) acc)
                csts UVars.empty_sort_subst
            in
            let inst = UVars.subst_sort_level_instance subst u in
            applist (mkConstU (cst, EInstance.make inst), params)
          | None -> bd
        end

let raw_rec_declaration (names, types, bodies) =
  (names, Array.map (fun c -> c.CbnClos.term) types, Array.map (fun c -> c.CbnClos.term) bodies)

let contract_cofix env sigma ?reference ?current_refold (bodynum,(names,types,bodies as typedbodies)) =
  let nbodies = Array.length bodies in
  let raw_typedbodies = raw_rec_declaration typedbodies in
  let base_subst = bodies.(bodynum).CbnClos.subst in
  let current_refold = Option.map
      (fun (cst, params) -> CbnClos.mk_app (CbnClos.inject cst) (List.rev params))
      current_refold in
  let make_Fi j =
    let ind = nbodies-j-1 in
    let bd = CbnClos.mk_clos base_subst (mkCoFix (ind,raw_typedbodies)) in
    if Int.equal bodynum ind then Option.default bd current_refold
    else match reference with
      | None -> bd
      | Some r ->
        CbnClos.inject (magically_constant_of_fixbody env sigma r (CbnClos.force sigma bd) names.(ind).binder_name) in
  let closure = List.init nbodies make_Fi in
  let subst = List.fold_right Esubst.subs_cons closure bodies.(bodynum).CbnClos.subst in
  CbnClos.mk_clos subst bodies.(bodynum).CbnClos.term

(** Similar to the "fix" case below *)
let singleton_best_cst = function
  | [_] as cst_l -> Cst_stack.best_cst cst_l
  | [] | _ :: _ :: _ -> None

let reduce_and_refold_cofix recfun env sigma cst_l ((_,(_,_,bodies)) as cofix) sk =
  let current_refold = singleton_best_cst cst_l in
  let reference =
    if Array.length bodies > 1 then Cst_stack.reference sigma (CbnClos.force sigma) cst_l
    else None
  in
  let raw_answer =
    contract_cofix env sigma ?reference ?current_refold cofix in
  let (x, (t, sk')) = apply_subst sigma Cst_stack.empty raw_answer sk in
  let t = match cst_l, current_refold with
    | [], _ | _, Some _ -> t
    | _ :: _, None ->
      let d = mkCoFix (CbnClos.force_cofix sigma cofix) in
      CbnClos.inject (Cst_stack.best_replace sigma (CbnClos.force sigma) d cst_l (CbnClos.force sigma t))
  in
  recfun x (t, sk')

(* contracts fix==FIX[nl;i](A1...Ak;[F1...Fk]{B1....Bk}) to produce
   Bi[Fj --> FIX[nl;j](A1...Ak;[F1...Fk]{B1...Bk})] *)

let contract_fix env sigma ?reference ?current_refold ((recindices,bodynum),(names,types,bodies as typedbodies)) =
    let nbodies = Array.length recindices in
    let raw_typedbodies = raw_rec_declaration typedbodies in
    let base_subst = bodies.(bodynum).CbnClos.subst in
    let current_refold = Option.map
        (fun (cst, params) -> CbnClos.mk_app (CbnClos.inject cst) (List.rev params))
        current_refold in
    let make_Fi j =
      let ind = nbodies-j-1 in
      let bd = CbnClos.mk_clos base_subst (mkFix ((recindices,ind),raw_typedbodies)) in
      if Int.equal bodynum ind then Option.default bd current_refold
      else match reference with
        | None -> bd
        | Some r -> CbnClos.inject (magically_constant_of_fixbody env sigma r (CbnClos.force sigma bd) names.(ind).binder_name) in
    let closure = List.init nbodies make_Fi in
    let subst = List.fold_right Esubst.subs_cons closure bodies.(bodynum).CbnClos.subst in
    CbnClos.mk_clos subst bodies.(bodynum).CbnClos.term

(** First we substitute the Rel bodynum by the fixpoint and then we try to
    replace the fixpoint by the best constant from [cst_l]
    Other rels are directly substituted by constants "magically found from the
    context" in contract_fix *)
let reduce_and_refold_fix recfun env sigma cst_l (((_,_),(_,_,bodies)) as fix) sk =
  let current_refold = singleton_best_cst cst_l in
  let reference =
    if Array.length bodies > 1 then Cst_stack.reference sigma (CbnClos.force sigma) cst_l
    else None
  in
  let raw_answer =
    contract_fix env sigma ?reference ?current_refold fix in
  let (x, (t, sk')) = apply_subst sigma Cst_stack.empty raw_answer sk in
  let t = match cst_l, current_refold with
    | [], _ | _, Some _ -> t
    | _ :: _, None ->
      let d = mkFix (CbnClos.force_fix sigma fix) in
      CbnClos.inject (Cst_stack.best_replace sigma (CbnClos.force sigma) d cst_l (CbnClos.force sigma t))
  in
  recfun x (t, sk')

module CredNative = Reductionops.CredNative

(** Generic reduction function with environment

    Here is where unfolded constant are stored in order to be
    eventually refolded.

    It uses ReductionBehaviour, prefers
    refold constant instead of value and tries to infer constants
    fix and cofix came from.

    It substitutes fix and cofix by the constant they come from in
    contract_* in any case .
*)

let debug_RAKAM = Reductionops.debug_RAKAM

let equal_stacks env sigma (x, l) (y, l') =
  let f_equal x y = CbnClos.equal sigma x y in
  let eq_fix a b =
    eq_constr sigma (mkFix (CbnClos.force_fix sigma a)) (mkFix (CbnClos.force_fix sigma b)) in
  let eq_case (ci1, u1, pms1, (p1,_), _, br1) (ci2, u2, pms2, (p2,_), _, br2) =
    let eq_under_ctx (nas1, c1) (nas2, c2) =
      Int.equal (Array.length nas1) (Array.length nas2) &&
      CbnClos.equal_under sigma (Array.length nas1) c1 c2
    in
    Array.equal f_equal pms1 pms2 &&
    eq_under_ctx p1 p2 &&
    Array.equal eq_under_ctx br1 br2
  in
  Stack.equal env f_equal eq_fix eq_case l l' && f_equal x y

let cbn_subst_of_rel_context_instance_list sign args subst =
  let open Context.Rel.Declaration in
  let rec aux subst sign l = match sign, l with
    | LocalAssum _ :: sign', a::args' -> aux (Esubst.subs_cons a subst) sign' args'
    | LocalDef (_,c,_)::sign', args' ->
      let c = CbnClos.mk_clos subst c in
      aux (Esubst.subs_cons c subst) sign' args'
    | [], [] -> subst
    | _ -> CErrors.anomaly (Pp.str "Instance and signature do not match.")
  in aux subst (List.rev sign) args

let apply_branch env sigma (ind, i) args (ci, u, pms, iv, r, lf) =
  let args = Stack.tail ci.ci_npar args in
  let args = Option.get (Stack.list_of_app_stack args) in
  let br = lf.(i - 1) in
  let body = snd br in
  let subst =
    if Int.equal ci.ci_cstr_nargs.(i - 1) ci.ci_cstr_ndecls.(i - 1) then
      (* No let-bindings *)
      List.fold_left (fun subst arg -> Esubst.subs_cons arg subst) body.CbnClos.subst args
    else
      let pms = Array.map (CbnClos.force sigma) pms in
      let ctx = expand_branch env sigma u pms (ind, i) (fst br, mkProp) in
      cbn_subst_of_rel_context_instance_list ctx args body.CbnClos.subst
  in
  CbnClos.mk_clos subst body.CbnClos.term


exception PatternFailure

let match_einstance sigma pu u psubst =
  match UVars.Instance.pattern_match pu (EInstance.kind sigma u) psubst with
  | Some psubst -> psubst
  | None -> raise PatternFailure

let match_sort ps s psubst =
  match Sorts.pattern_match ps s psubst with
  | Some psubst -> psubst
  | None -> raise PatternFailure

let rec match_arg_pattern whrec env sigma ctx psubst p t =
  let open Declarations in
  match p with
  | EHole i ->
      let t = CbnClos.force sigma t in
      let t' = EConstr.it_mkLambda_or_LetIn t ctx in
      Partial_subst.add_term i t' psubst
  | EHoleIgnored -> psubst
  | ERigid (ph, es) ->
      let t, stk = whrec ctx (t, Stack.empty) in
      let psubst = match_rigid_arg_pattern whrec env sigma ctx psubst ph t in
      let psubst, stk = apply_rule whrec env sigma ctx psubst es stk in
      match stk with
      | [] -> psubst
      | _ :: _ -> raise PatternFailure

and match_rigid_arg_pattern whrec env sigma ctx psubst p t =
  match [@ocaml.warning "-4"] p, CbnClos.kind sigma t with
  | PHInd (ind, pu), NotArray Ind (ind', u) ->
    if QInd.equal env ind ind' then match_einstance sigma pu u psubst else raise PatternFailure
  | PHConstr (constr, pu), NotArray Construct (constr', u) ->
    if QConstruct.equal env constr constr' then match_einstance sigma pu u psubst else raise PatternFailure
  | PHRel i, NotArray Rel n when i = n -> psubst
  | PHSort ps, NotArray Sort s -> match_sort ps (ESorts.kind sigma s) psubst
  | PHSymbol (c, pu), NotArray Const (c', u) ->
    if QConstant.equal env c c' then match_einstance sigma pu u psubst else raise PatternFailure
  | PHInt i, NotArray Int i' ->
    if Uint63.equal i i' then psubst else raise PatternFailure
  | PHFloat f, NotArray Float f' ->
    if Float64.equal f f' then psubst else raise PatternFailure
  | PHString s, NotArray String s' ->
    if Pstring.equal s s' then psubst else raise PatternFailure
  | PHLambda (ptys, pbod), _ ->
    let t = CbnClos.force sigma t in
    let ntys, _ = EConstr.decompose_lambda sigma t in
    let na = List.length ntys and np = Array.length ptys in
    if np > na then raise PatternFailure;
    let ntys, body = EConstr.decompose_lambda_n sigma np t in
    let ctx' = List.map (fun (n, ty) -> Context.Rel.Declaration.LocalAssum (n, ty)) ntys in
    let tys = Array.of_list @@ List.rev_map snd ntys in
    let na = Array.length tys in
    let contexts_upto = Array.init na (fun i -> List.skipn (na - i) ctx' @ ctx) in
    let tys = Array.map CbnClos.inject tys in
    let psubst = Array.fold_left3 (fun psubst ctx -> match_arg_pattern whrec env sigma ctx psubst) psubst contexts_upto ptys tys in
    let psubst = match_arg_pattern whrec env sigma (ctx' @ ctx) psubst (ERigid pbod) (CbnClos.inject body) in
    psubst
  | PHProd (ptys, pbod), _ ->
    let t = CbnClos.force sigma t in
    let ntys, _ = EConstr.decompose_prod sigma t in
    let na = List.length ntys and np = Array.length ptys in
    if np > na then raise PatternFailure;
    let ntys, body = EConstr.decompose_prod_n sigma np t in
    let ctx' = List.map (fun (n, ty) -> Context.Rel.Declaration.LocalAssum (n, ty)) ntys in
    let tys = Array.of_list @@ List.rev_map snd ntys in
    let na = Array.length tys in
    let contexts_upto = Array.init na (fun i -> List.skipn (na - i) ctx' @ ctx) in
    let tys = Array.map CbnClos.inject tys in
    let psubst = Array.fold_left3 (fun psubst ctx -> match_arg_pattern whrec env sigma ctx psubst) psubst contexts_upto ptys tys in
    let psubst = match_arg_pattern whrec env sigma (ctx' @ ctx) psubst pbod (CbnClos.inject body) in
    psubst
  | (PHInd _ | PHConstr _ | PHRel _ | PHInt _ | PHFloat _ | PHString _ | PHSort _ | PHSymbol _), _ -> raise PatternFailure

and extract_n_stack args n s =
  if n = 0 then List.rev args, s else
  match Stack.decomp s with
  | Some (arg, rest) -> extract_n_stack (arg :: args) (n-1) rest
  | None -> raise PatternFailure

and apply_rule whrec env sigma ctx psubst es stk =
  match [@ocaml.warning "-4"] es, stk with
  | [], _ -> psubst, stk
  | Declarations.PEApp pargs :: e, s ->
      let np = Array.length pargs in
      let pargs = Array.to_list pargs in
      let args, s = extract_n_stack [] np s in
      let psubst = List.fold_left2 (match_arg_pattern whrec env sigma ctx) psubst pargs args in
      apply_rule whrec env sigma ctx psubst e s
  | Declarations.PECase (pind, pret, pbrs) :: e, Stack.Case ((ci, u, pms, p, iv, brs), cst_l) :: s ->
      if not @@ QInd.equal env pind ci.ci_ind then raise PatternFailure;
      let dummy = mkProp in
      let pms = Array.map (CbnClos.force sigma) pms in
      let p = CbnClos.force_return sigma p in
      let brs = CbnClos.force_branches sigma brs in
      let (_, _, _, ((ntys_ret, ret), _), _, _, brs) = EConstr.annotate_case env sigma (ci, u, pms, p, NoInvert, dummy, brs) in
      let psubst = match_arg_pattern whrec env sigma (ntys_ret @ ctx) psubst pret (CbnClos.inject ret) in
      let psubst = Array.fold_left2 (fun psubst pat (ctx', br) -> match_arg_pattern whrec env sigma (ctx' @ ctx) psubst pat (CbnClos.inject br)) psubst pbrs brs in
      apply_rule whrec env sigma ctx psubst e s
  | Declarations.PEProj proj :: e, Stack.Proj (proj', r, cst_l') :: s ->
      if not @@ QProjection.Repr.equal env proj (Projection.repr proj') then raise PatternFailure;
      apply_rule whrec env sigma ctx psubst e s
  | _, _ -> raise PatternFailure


let rec apply_rules whrec env sigma u r stk =
  let open Declarations in
  match r with
  | [] -> raise PatternFailure
  | { lhs_pat = (pu, elims); nvars; rhs } :: rs ->
    try
      let psubst = Partial_subst.make nvars in
      let psubst = match_einstance sigma pu u psubst in
      let psubst, stk = apply_rule whrec env sigma [] psubst elims stk in
      let subst, qsubst, usubst = Partial_subst.to_arrays psubst in
      let usubst = UVars.Instance.of_array (qsubst, usubst) in
      let rhsu = subst_instance_constr (EConstr.EInstance.make usubst) (EConstr.of_constr rhs) in
      let rhs' = substl (Array.to_list subst) rhsu in
      (CbnClos.inject rhs', stk)
    with PatternFailure -> apply_rules whrec env sigma u rs stk




let rec whd_state_gen ?csts flags env sigma =
  let open Context.Named.Declaration in
  let open ReductionBehaviour in
  let rec whrec cst_l (x, stack) =
    let () = debug_RAKAM (fun () ->
        let open Pp in
        let pr c = Termops.Internal.print_constr_env env sigma (CbnClos.force sigma c) in
               (h (str "<<" ++ pr x ++
                   str "|" ++ cut () ++ Cst_stack.pr env sigma pr cst_l ++
                   str "|" ++ cut () ++ Stack.pr pr stack ++
                   str ">>")))
    in
    let reduce_primitive_value () =
      match Stack.strip_app stack with
      | (_, Stack.Primitive(p,(_,u as kn),rargs,kargs,cst_l')::s) ->
        let more_to_reduce = List.exists (fun k -> CPrimitives.Kwhnf = k) kargs in
        if more_to_reduce then
          let (kargs,o) = Stack.get_next_primitive_args kargs s in
          (* Should not fail because Primitive is put on the stack only if fully applied *)
          let (before,a,after) = Option.get o in
          Some (whrec Cst_stack.empty (a,Stack.Primitive(p,kn,rargs @ Stack.append_app [|x|] before,kargs,cst_l')::after))
        else
          let n = List.length kargs in
          let (args,s) = Stack.strip_app s in
          let (args,extra_args) =
            try List.chop n args
            with List.IndexOutOfRange -> (args,[]) (* FIXME probably useless *)
          in
          let s = extra_args @ s in
          let args = Option.get (Stack.list_of_app_stack (rargs @ Stack.append_app [|x|] args)) in
          let args = Array.of_list args in
          Some
            (match reduce_array_primitive sigma u p args with
             | Some t -> whrec cst_l' (t,s)
             | None ->
               let args = Array.map (CbnClos.force sigma) args in
               match CredNative.red_prim env sigma p u args with
               | Some t -> whrec cst_l' (CbnClos.inject t,s)
               | None -> ((CbnClos.inject (mkApp (mkConstU kn, args)), s), cst_l))
      | _ -> None
    in
    let fold () =
      let () = debug_RAKAM (fun () ->
          Pp.(str "<><><><><>")) in
      ((x, stack),cst_l)
    in
    let c0 = CbnClos.kind sigma x in
    match c0 with
    | NotArray Rel n when RedFlags.red_set flags RedFlags.fDELTA ->
      (match lookup_rel n env with
      | LocalDef (_,body,_) -> whrec Cst_stack.empty (CbnClos.lift n (CbnClos.inject body), stack)
      | _ -> fold ())
    | NotArray Var id when RedFlags.red_set flags (RedFlags.fVAR id) ->
      (match lookup_named id env with
      | LocalDef (_,body,_) ->
        whrec (Cst_stack.add_cst (mkVar id) cst_l) (CbnClos.inject body, stack)
      | _ -> fold ())
    | NotArray Evar _ | NotArray Meta _ -> fold ()
    | NotArray Const (c,u as const) ->
      Reductionops.reduction_effect_hook env sigma c
         (lazy (EConstr.to_constr sigma (stack_zip sigma (x,fst (Stack.strip_app stack)))));
      if RedFlags.red_set flags (RedFlags.fCONST c) then
       let u' = EInstance.kind sigma u in
       match constant_value_in env sigma (c, u) with
       | body ->
         begin
          (* Looks for ReductionBehaviour *)
            match ReductionBehaviour.get c with
            | None -> whrec (Cst_stack.add_cst (mkConstU const) cst_l) (CbnClos.inject body, stack)
            | Some behavior ->
              begin match behavior with
              | NeverUnfold -> fold ()
              | (UnfoldWhen { nargs = Some n } |
                 UnfoldWhenNoMatch { nargs = Some n } )
                when Stack.args_size stack < n ->
                fold ()
              | UnfoldWhenNoMatch { recargs; nargs } -> (* maybe unfolds *)
                  let app_sk,sk = Stack.strip_app stack in
                  let volatile = Option.has_some nargs in
                  let rec is_case x = match CbnClos.kind sigma x with
                    | NotArray Lambda (_,_, x) | NotArray LetIn (_,_,_, x) -> is_case (CbnClos.liftn 1 x)
                    | NotArray Cast (x, _,_) -> is_case x
                    | NotArray App (hd, _) -> is_case hd
                    | NotArray Case _ -> true
                    | _ -> false in
                  let local_rel_is_unfoldable n =
                    RedFlags.red_set flags RedFlags.fDELTA &&
                    match lookup_rel n env with
                    | LocalDef _ -> true
                    | LocalAssum _ -> false
                    | exception Not_found -> false
                  in
                  let local_var_is_unfoldable id =
                    RedFlags.red_set flags (RedFlags.fVAR id) &&
                    match lookup_named id env with
                    | LocalDef _ -> true
                    | LocalAssum _ -> false
                    | exception Not_found -> false
                  in
                  (* Fast-path substitutions that are already stuck.  If the
                     substituted value can still make head progress (local
                     definitions, transparent constants, lets, beta-redexes,
                     fixpoints, projections, ...), fall back to the ordinary
                     weak-head pass below.  That pass is what notices that a
                     [simpl nomatch] wrapper would expose a stuck case after
                     zeta/delta/beta reduction and therefore refolds it. *)
                  let rec is_obviously_stuck tm sk =
                    not (Stack.will_expose_iota sk) &&
                    match CbnClos.kind sigma tm with
                    | NotArray Cast (tm, _, _) -> is_obviously_stuck tm sk
                    | NotArray App (hd, args) -> is_obviously_stuck hd (Stack.append_app args sk)
                    | NotArray Rel n -> not (local_rel_is_unfoldable n)
                    | NotArray Var id -> not (local_var_is_unfoldable id)
                    | NotArray Const (c, _) -> not (RedFlags.red_set flags (RedFlags.fCONST c))
                    | NotArray Lambda _ -> Option.is_empty (Stack.decomp sk)
                    | NotArray Construct _ | NotArray Ind _ | NotArray Evar _ | NotArray Meta _ | NotArray Sort _ | NotArray Prod _
                    | NotArray Int _ | NotArray Float _ | NotArray String _ | Array _ -> true
                    | NotArray LetIn _ | NotArray Case _ | NotArray Fix _ | NotArray CoFix _ | NotArray Proj _ -> false
                    | NotArray Array _ -> assert false
                  in
                  let unfolds_to_subst_value = match recargs with
                    | _ :: _ -> None
                    | [] ->
                      let cst_l' = Cst_stack.add_cst ~volatile ~refold_after_iota:true (mkConstU const) cst_l in
                      let cst_l', (tm', sk') =
                        apply_subst sigma cst_l' (CbnClos.inject body) app_sk in
                      match CbnClos.subst_value sigma tm' with
                      | Some tm' when is_obviously_stuck tm' sk' ->
                        Some ((tm', sk'), cst_l')
                      | Some _ | None -> None
                  in
                  begin match unfolds_to_subst_value with
                  | Some ((tm', sk'), cst_l') -> whrec cst_l' (tm', sk' @ sk)
                  | None ->
                    let (tm',sk'),cst_l' =
                      match recargs with
                      | [] ->
                        let cst_l = Cst_stack.add_cst ~volatile ~refold_after_iota:true
                            (mkConstU const) cst_l in
                        whrec cst_l (CbnClos.inject body, app_sk)
                      | curr :: remains -> match Stack.strip_n_app curr app_sk with
                        | None -> (x,app_sk), cst_l
                        | Some (bef,arg,app_sk') ->
                          let cst_l = Stack.Cst
                              { const = Stack.Cst_const (fst const, u');
                                volatile;
                                refold_after_iota = true;
                                curr; remains; params=bef; cst_l;
                              }
                          in
                          whrec Cst_stack.empty (arg,cst_l :: app_sk')
                    in
                    (* If the selected recursive argument definitely changed,
                       the unfolded state cannot be equal to the original one;
                       avoid a full stack comparison, which may force unrelated
                       arguments only to discard the equality result. *)
                    let recarg_changed = match recargs with
                      | [] -> false
                      | curr :: _ ->
                        not (CbnClos.equal sigma x tm') ||
                        match Stack.strip_n_app curr app_sk, Stack.strip_n_app curr sk' with
                        | Some (_, arg, _), Some (_, arg', _) ->
                          not (CbnClos.equal sigma arg arg')
                        | _ -> false
                    in
                    if (not recarg_changed && equal_stacks env sigma (x, app_sk) (tm', sk'))
                    || Stack.will_expose_iota sk'
                    || is_case tm'
                    then fold ()
                    else whrec cst_l' (tm', sk' @ sk)
                  end
              | UnfoldWhen { recargs; nargs } -> (* maybe unfolds *)
                begin match recargs with
                  | [] -> (* if nargs has been specified *)
                    (* CAUTION : the constant is NEVER refolded (even when it hides a (co)fix) *)
                    whrec cst_l (CbnClos.inject body, stack)
                  | curr :: remains -> match Stack.strip_n_app curr stack with
                    | None -> fold ()
                    | Some (bef,arg,s') ->
                      let cst_l = Stack.Cst
                          { const = Stack.Cst_const (fst const, u');
                            volatile = Option.has_some nargs;
                            refold_after_iota = false;
                            curr; remains; params=bef; cst_l;
                          }
                      in
                      whrec Cst_stack.empty (arg,cst_l::s')
                end
              end
        end
       | exception NotEvaluableConst (IsPrimitive (u,p)) when Stack.check_native_args p stack ->
          let kargs = CPrimitives.kind p in
          let (kargs,o) = Stack.get_next_primitive_args kargs stack in
          (* Should not fail thanks to [check_native_args] *)
          let (before,a,after) = Option.get o in
          whrec Cst_stack.empty (a,Stack.Primitive(p,const,before,kargs,cst_l)::after)
       | exception NotEvaluableConst (HasRules (u', b, r)) ->
          begin try
            let red_fun ctx =
              let env = push_rel_context ctx env in
              whd_state_gen flags env sigma
            in
            let rhs_stack = apply_rules red_fun env sigma u r stack in
            whrec Cst_stack.empty rhs_stack
          with PatternFailure ->
            if not b then fold () else
            match Stack.strip_app stack with
            | args, (Stack.Fix (f,s',cst_l)::s'') when RedFlags.red_set flags RedFlags.fFIX ->
                let x' = clos_of_app_stack sigma x args in
                let out_sk = s' @ (Stack.append_app [|x'|] s'') in
                reduce_and_refold_fix whrec env sigma cst_l f out_sk
            | _ -> fold ()
          end
       | exception NotEvaluableConst _ -> fold ()
      else fold ()
    | NotArray Proj (p, r, c) when RedFlags.red_projection flags p ->
      (let npars = Projection.npars p in
       match ReductionBehaviour.get (Projection.constant p) with
         | None ->
           let stack' = (c, Stack.Proj (p, r, cst_l) :: stack) in
           let stack'', csts = whrec Cst_stack.empty stack' in
           if equal_stacks env sigma stack' stack'' then fold ()
           else stack'', csts
         | Some behavior ->
           begin match behavior with
             | NeverUnfold -> fold ()
             | (UnfoldWhen { nargs = Some n }
               | UnfoldWhenNoMatch { nargs = Some n })
               when Stack.args_size stack < n - (npars + 1) -> fold ()
             | UnfoldWhen { recargs }
             | UnfoldWhenNoMatch { recargs }-> (* maybe unfolds *)
               let recargs = List.map_filter (fun x ->
                   let idx = x - npars in
                   if idx < 0 then None else Some idx) recargs
               in
               let volatile = match behavior with
                 | UnfoldWhen {nargs} -> Option.has_some nargs
                 | UnfoldWhenNoMatch _ | NeverUnfold -> false
               in
               match recargs with
               | [] -> (* if nargs has been specified *)
                 (* CAUTION : the constant is NEVER refold
                                  (even when it hides a (co)fix) *)
                 let stack' = (c, Stack.Proj (p, r, cst_l) :: stack) in
                 whrec Cst_stack.empty(* cst_l *) stack'
               | curr :: remains ->
                 match Stack.strip_n_app curr (Stack.append_app [|c|] stack) with
                 | None -> fold ()
                 | Some (bef,arg,s') ->
                   let cst_l = Stack.Cst
                       { const=Stack.Cst_proj (p,r);
                         curr;
                         remains;
                         volatile;
                         refold_after_iota =
                           (match behavior with
                            | UnfoldWhenNoMatch _ -> true
                            | UnfoldWhen _ | NeverUnfold -> false);
                         params=bef;
                         cst_l;
                       }
                   in
                   whrec Cst_stack.empty (arg,cst_l::s')
           end)

    | NotArray LetIn (_,b,_,c) when RedFlags.red_set flags RedFlags.fZETA ->
      whrec cst_l (CbnClos.subst_cons b c, stack)
    | NotArray Cast (c,_,_) -> whrec cst_l (c, stack)
    | NotArray App (f,cl)  ->
      whrec
        (Cst_stack.add_args cl cst_l)
        (f, Stack.append_app cl stack)
    | NotArray Lambda (na,t,c) ->
      (match Stack.decomp stack with
      | Some _ when RedFlags.red_set flags RedFlags.fBETA ->
        let (cst_l, p) = apply_subst sigma cst_l x stack in
        whrec cst_l p
      | _ -> fold ())

    | NotArray Case (ci,u,pms,p,iv,d,lf) ->
      whrec Cst_stack.empty (d, Stack.Case ((ci,u,pms,p,iv,lf),cst_l) :: stack)

    | NotArray Fix ((ri,n),_ as f) ->
      (match Stack.strip_n_app ri.(n) stack with
      |None -> fold ()
      |Some (bef,arg,s') ->
        whrec Cst_stack.empty (arg, Stack.Fix(f,bef,cst_l)::s'))

    | NotArray Construct (cstr ,u) ->
      let use_match = RedFlags.red_set flags RedFlags.fMATCH in
      let use_fix = RedFlags.red_set flags RedFlags.fFIX in
      if use_match || use_fix then
        match Stack.strip_app stack with
        |args, (Stack.Case(case,case_cst_l)::s') when use_match ->
          let r = apply_branch env sigma cstr args case in
          let rec is_case x = match CbnClos.kind sigma x with
            | NotArray Lambda (_,_, x) | NotArray LetIn (_,_,_, x) -> is_case (CbnClos.liftn 1 x)
            | NotArray Cast (x, _,_) -> is_case x
            | NotArray App (hd, _) -> is_case hd
            | NotArray Case _ -> true
            | _ -> false
          in
          let reduce_with_elim_csts cst_l p =
            match cst_l, case_cst_l with
            | [], _ :: _ when Cst_stack.may_refold_alias_after_iota case_cst_l && is_case r ->
              (* [simpl nomatch] wrappers, including projection wrappers using
                 [UnfoldWhenNoMatch], must stay folded when reducing under them
                 exposes a stuck eliminator.  Do not do this for ordinary
                 transparent aliases, even when the alias result has pending
                 eliminations: after a real iota step master keeps the progress
                 and reduces aliases such as [fst_nat] and [id_fun] away. *)
              let (_, cst_l') as res = whrec case_cst_l p in
              begin match cst_l' with
              | [] -> res
              | _ :: _ -> whrec Cst_stack.empty p
              end
            | [], [] | [], _ :: _ | _ :: _, _ -> whrec Cst_stack.empty p
          in
          reduce_with_elim_csts cst_l (r, s')
        |args, (Stack.Proj (p,_,_)::s') when use_match ->
          whrec Cst_stack.empty (Stack.nth args (Projection.npars p + Projection.arg p), s')
        |args, (Stack.Fix (f,s',cst_l)::s'') when use_fix ->
          let x' = clos_of_app_stack sigma x args in
          let out_sk = s' @ (Stack.append_app [|x'|] s'') in
          reduce_and_refold_fix whrec env sigma cst_l f out_sk
        |args, (Stack.Cst {const;curr;remains;volatile;refold_after_iota;params=s';cst_l} :: s'') ->
          let x' = clos_of_app_stack sigma x args in
          begin match remains with
          | [] ->
            (match const with
            | Stack.Cst_const const ->
              (match constant_opt_value_in env const with
              | None -> fold ()
              | Some body ->
                let const = (fst const, EInstance.make (snd const)) in
                let body = EConstr.of_constr body in
                let cst_l = Cst_stack.add_cst ~volatile ~refold_after_iota (mkConstU const) cst_l in
                whrec cst_l (CbnClos.inject body, s' @ (Stack.append_app [|x'|] s'')))
            | Stack.Cst_proj (p,r) ->
              let stack = s' @ (Stack.append_app [|x'|] s'') in
              match Stack.strip_n_app 0 stack with
              | None -> assert false
              | Some (_,arg,s'') ->
                whrec Cst_stack.empty (arg, Stack.Proj (p,r,cst_l) :: s''))
          | next :: remains' -> match Stack.strip_n_app (next-curr-1) s'' with
            | None -> fold ()
            | Some (bef,arg,s''') ->
              let cst_l = Stack.Cst
                  { const;
                    curr=next;
                    volatile;
                    refold_after_iota;
                    remains=remains';
                    params=s' @ (Stack.append_app [|x'|] bef);
                    cst_l;
                  }
              in
              whrec Cst_stack.empty (arg, cst_l :: s''')
          end
        |_, (Stack.App _)::_ -> assert false
        |_, _ -> fold ()
      else fold ()

    | NotArray CoFix cofix ->
      if RedFlags.red_set flags RedFlags.fCOFIX then
        match Stack.strip_app stack with
        |args, ((Stack.Case _ |Stack.Proj _)::s') ->
          reduce_and_refold_cofix whrec env sigma cst_l cofix stack
        |_ -> fold ()
      else fold ()

    | NotArray Int _ | NotArray Float _ | NotArray String _ | Array _ ->
      begin match reduce_primitive_value () with
      | Some res -> res
      | None ->
      begin match Stack.strip_app stack with
        |args, (Stack.Cst {const;curr;remains;volatile;refold_after_iota;params=s';cst_l} :: s'') ->
          let x' = clos_of_app_stack sigma x args in
          begin match remains with
          | [] ->
            (match const with
            | Stack.Cst_const const ->
              (match constant_opt_value_in env const with
              | None -> fold ()
              | Some body ->
                let const = (fst const, EInstance.make (snd const)) in
                let body = EConstr.of_constr body in
                let cst_l = Cst_stack.add_cst ~volatile ~refold_after_iota (mkConstU const) cst_l in
                whrec cst_l (CbnClos.inject body, s' @ (Stack.append_app [|x'|] s'')))
            | Stack.Cst_proj (p,r) ->
              let stack = s' @ (Stack.append_app [|x'|] s'') in
              match Stack.strip_n_app 0 stack with
              | None -> assert false
              | Some (_,arg,s'') ->
                whrec Cst_stack.empty (arg, Stack.Proj (p,r,cst_l) :: s''))
          | next :: remains' -> match Stack.strip_n_app (next-curr-1) s'' with
            | None -> fold ()
            | Some (bef,arg,s''') ->
              let cst_l = Stack.Cst
                  { const;
                    curr=next;
                    volatile;
                    refold_after_iota;
                    remains=remains';
                    params=s' @ (Stack.append_app [|x'|] bef);
                    cst_l;
                  }
              in
              whrec Cst_stack.empty (arg, cst_l :: s''')
          end
       | _ -> fold ()
      end
      end

    | NotArray Rel _ | NotArray Var _ | NotArray LetIn _ | NotArray Proj _ -> fold ()
    | NotArray Sort _ | NotArray Ind _ | NotArray Prod _ -> fold ()
    | NotArray Array _ -> assert false
  in
  fun xs ->
  let (s,cst_l) = whrec (Option.default Cst_stack.empty csts) xs in
  Stack.best_state ~inject:CbnClos.inject ~equal:(CbnClos.equal sigma) s cst_l

let whd_cbn flags env sigma t =
  let state = whd_state_gen flags env sigma (CbnClos.inject t, Stack.empty) in
  stack_zip ~refold:true sigma state

let norm_cbn flags env sigma t =
  let push_rel_check_zeta d env =
    let open RedFlags in
    let d = match d with
      | LocalDef (na,_,t) when not (red_set flags fZETA) -> LocalAssum (na,t)
      | d -> d in
    push_rel d env
  in
  (* Refold the weak-head state before descending recursively.  If we map over
     the delayed stack directly, application arguments are normalized before
     enclosing case/fix/constant frames can refold or discard them. *)
  let rec strongrec env t =
    Termops.map_constr_with_full_binders env sigma
      push_rel_check_zeta strongrec env (whd_cbn flags env sigma t)
  in
  strongrec env t
