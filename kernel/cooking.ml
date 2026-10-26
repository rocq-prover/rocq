(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Created by Jean-Christophe Filliâtre out of V6.3 file constants.ml
   as part of the rebuilding of Coq around a purely functional
   abstract type-checker, Nov 1999 *)

(* This module implements kernel-level discharching of local
   declarations over global constants and inductive types *)

open Util
open Names
open Term
open Constr
open UVars
open Context

module NamedDecl = Context.Named.Declaration

(** {6 Data needed to abstract over the section variables and section universes } *)

(** The generalization to be done on a specific judgment:
    [a:T,b:U,c:V(a) ⊢ w(a,c):W(a,c)
     ~~>
     ⊢ λxz.w(a,c)[a,c:=x,z]:(Πx:T.z:T(a).W(a,c))[a,c:=x,z]]
    so, an abstr_info is both the context x:T,z:V(x) to generalize
    (skipping y which does not occur), and the substitution [a↦x,c↦z]
    where in practice, x and z are canonical (hence implicit) de
    Bruijn indices, that is, only the instantiation [a,c] is kept *)

type abstr_info = {
  abstr_ctx : Constr.named_context;
  (** Context over which to generalize (e.g. x:T,z:V(x)) *)
  abstr_auctx : UVars.AbstractContext.t;
  (** Universe context over which to generalize *)
  abstr_ausubst : Instance.t;
  (** Universe substitution represented as an instance *)
}

(** The instantiation to apply to generalized declarations so that
    they behave as if not generalized: this is the a1..an instance to
    apply to a declaration c in the following transformation:
    [a1:T1..an:Tn, C:U(a1..an) ⊢ v(a1..an,C):V(a1..an,C)
     ~~>
     C:Πx1..xn.U(x1..xn), a1:T1..an:Tn ⊢ v(a1..an,Ca1..an):V(a1..an,Ca1..an)]
    note that the data looks close to the one for substitution above
    (because the substitution are represented by their domain) but
    here, local definitions of the context have been dropped *)

type abstr_inst_info = {
  abstr_rev_inst : Id.t list;
  (** The variables to reapply (excluding "let"s of the context), in reverse order *)
  abstr_uinst : UVars.Instance.t;
  (** Abstracted universe variables to reapply *)
}

(** The collection of instantiations to apply to generalized
    declarations so that they behave as if not generalized.
    This accounts for the permutation (lambda-lifting) of global and
    local declarations.
    Using the notations above, a expand_info is a map [c ↦ a1..an]
    over all generalized global declarations of the section *)

type 'a entry_map = 'a Cmap.t * 'a Mindmap.t
type expand_info = abstr_inst_info entry_map

(** The collection of instantiations to be done on generalized
    declarations + the generalization to be done on a specific
    judgment:
    [a1:T1,a2:T2,C:U(a1) ⊢ v(a1,a2,C):V(a1,a2,C)
     ~~>
     c:Πx.U(x) ⊢ λx1x2.(v(a1,a2,cx1)[a1,a2:=x1,x2]):Πx1x2.(V(a1,a2,ca1)[a1,a2:=x1,x2])]
    so, a cooking_info is the map [c ↦ x1..xn],
    the context x:T,y:U to generalize, and the substitution [x,y] *)

type cooking_info = {
  expand_info : expand_info;
  abstr_info : abstr_info;
}

let empty_cooking_info = {
  expand_info = (Cmap.empty, Mindmap.empty);
  abstr_info = {
      abstr_ctx = [];
      abstr_auctx = AbstractContext.empty;
      abstr_ausubst = Instance.empty;
    };
}

(*s Cooking the constants. *)

type my_global_reference =
  | ConstRef of Constant.t
  | IndRef of inductive
  | ConstructRef of constructor

module RefHash =
struct
  type t = my_global_reference
  let equal gr1 gr2 = match gr1, gr2 with
  | ConstRef c1, ConstRef c2 -> Constant.UserOrd.equal c1 c2
  | IndRef i1, IndRef i2 -> Ind.UserOrd.equal i1 i2
  | ConstructRef c1, ConstructRef c2 -> Construct.UserOrd.equal c1 c2
  | _ -> false
  open Hashset.Combine
  let hash = function
  | ConstRef c -> combinesmall 1 (Constant.UserOrd.hash c)
  | IndRef i -> combinesmall 2 (Ind.UserOrd.hash i)
  | ConstructRef c -> combinesmall 3 (Construct.UserOrd.hash c)
end

module RefTable = Hashtbl.Make(RefHash)
type internal_abstr_inst_info = UVars.Instance.t * int list * int

type cooking_cache = {
  cache : internal_abstr_inst_info RefTable.t;
  info : cooking_info;
  rel_ctx : rel_context Lazy.t;
}

let instantiate_my_gr gr u =
  match gr with
  | ConstRef c -> mkConstU (c, u)
  | IndRef i -> mkIndU (i, u)
  | ConstructRef c -> mkConstructU (c, u)

let discharge_inst top_abst_subst sub_abst_rev_inst =
  let rec aux k relargs top_abst_subst sub_abst_rev_inst =
    match top_abst_subst, sub_abst_rev_inst with
    | decl :: top_abst_subst, id' :: sub_abst_rev_inst' ->
      if Id.equal (NamedDecl.get_id decl) id' then
        aux (k+1) (k :: relargs) top_abst_subst sub_abst_rev_inst'
      else
        aux (k+1) relargs top_abst_subst sub_abst_rev_inst
    | _, [] -> relargs
    | [], _ -> assert false in
  aux 1 [] top_abst_subst sub_abst_rev_inst

let rec find_var k id = function
| [] -> raise Not_found
| decl :: subst ->
  if Id.equal id (NamedDecl.get_id decl) then k+1
  else find_var (k+1) id subst

let share cache top_abst_subst r (cstl,knl) =
  try RefTable.find cache r
  with Not_found ->
  let {abstr_uinst;abstr_rev_inst} =
    match r with
    | IndRef (kn,_i) -> Mindmap.find kn knl
    | ConstructRef ((kn,_i),_j) -> Mindmap.find kn knl
    | ConstRef cst -> Cmap.find cst cstl
  in
  let inst = (abstr_uinst, discharge_inst top_abst_subst abstr_rev_inst, List.length abstr_rev_inst) in
  RefTable.add cache r inst;
  inst

let make_inst k abstr_inst_rel =
  Array.map_of_list (fun n -> mkRel (k+n)) abstr_inst_rel

let share_univs cache top_abst_subst k r u l =
  let (abstr_uinst,abstr_inst_rel,_) = share cache top_abst_subst r l in
  mkApp (instantiate_my_gr r (Instance.append abstr_uinst u), make_inst k abstr_inst_rel)

let discharge_proj_repr r p = (* To merge with discharge_proj *)
  let nnewpars = List.count NamedDecl.is_local_assum r.abstr_info.abstr_ctx in
  let map npars = npars + nnewpars in
  Projection.Repr.map_npars map p

let discharge_proj (_,_,abstr_inst_length) p =
  let map npars = npars + abstr_inst_length in
  Projection.map_npars map p

let is_empty_modlist (cm, mm) =
  Cmap.is_empty cm && Mindmap.is_empty mm

let expand_constr ?(depth=0) cache modlist top_abst_subst c =
  let share_univs = share_univs cache top_abst_subst in
  let rec substrec k c =
    match kind c with
      | Case (ci, u, pms, p, iv, t, br) ->
        begin match share cache top_abst_subst (IndRef ci.ci_ind) modlist with
        | (abstr_uinst, abstr_inst_rel, abstr_inst_length) ->
          let u = Instance.append abstr_uinst u in
          let pms = Array.append (make_inst k abstr_inst_rel) pms in
          let ci = { ci with ci_npar = ci.ci_npar + abstr_inst_length } in
          Constr.map_with_binders succ substrec k (mkCase (ci,u,pms,p,iv,t,br))
        | exception Not_found ->
          Constr.map_with_binders succ substrec k c
        end

      | Ind (ind,u) ->
          (try
            share_univs k (IndRef ind) u modlist
           with
            | Not_found -> Constr.map_with_binders succ substrec k c)

      | Construct (cstr,u) ->
          (try
             share_univs k (ConstructRef cstr) u modlist
           with
            | Not_found -> Constr.map_with_binders succ substrec k c)

      | Const (cst,u) ->
          (try
            share_univs k (ConstRef cst) u modlist
           with
            | Not_found -> Constr.map_with_binders succ substrec k c)

      | Proj (p, r, c') ->
          let ind = Names.Projection.inductive p in
          let p' =
            try
              let exp = share cache top_abst_subst (IndRef ind) modlist in
              discharge_proj exp p
            with Not_found -> p in
          let c'' = substrec k c' in
          if p == p' && c' == c'' then c else mkProj (p', r, c'')

      | Var id ->
          (try
            mkRel (find_var k id top_abst_subst)
           with Not_found -> c)

  | _ -> Constr.map_with_binders succ substrec k c

  in
  if is_empty_modlist modlist && List.is_empty top_abst_subst then c
  else substrec depth c

(** A memo from a compound term and a binder depth to a term, the terms
    compared physically, for [expand_constr_shared]. A term that expands to
    itself does so at every depth, and is entered with depth [-1]. The memo is
    lossy: an entry whose few probe slots are all taken overwrites one of them,
    so keys that share a hash cost a recomputation, never a long scan. A lost
    entry only costs sharing and time, never a different result. *)
module ShareMemo = struct
  type t = {
    mutable keys : constr array;
    mutable depths : int array;
    mutable values : constr array;
    mutable count : int;
  }

  (* never a key: only compound terms are entered *)
  let no_key = mkProp
  let probes = 8
  let max_size = 1 lsl 22

  let make size =
    { keys = Array.make size no_key; depths = Array.make size 0;
      values = Array.make size no_key; count = 0 }

  let create () = make 1024

  (* [h] is [Constr.hash_bounded c] *)
  let find m h c k =
    let mask = Array.length m.keys - 1 in
    let h = Hashset.Combine.combine h k in
    let rec probe i =
      if Int.equal i probes then None
      else
        let j = (h + i) land mask in
        let key = Array.unsafe_get m.keys j in
        if key == no_key then None
        else if key == c && Int.equal (Array.unsafe_get m.depths j) k then
          Some (Array.unsafe_get m.values j)
        else probe (i + 1)
    in
    probe 0

  let insert m h c k v =
    let mask = Array.length m.keys - 1 in
    let h = Hashset.Combine.combine h k in
    let rec probe i =
      if Int.equal i probes then h land mask (* all taken: overwrite the first *)
      else
        let j = (h + i) land mask in
        if Array.unsafe_get m.keys j == no_key then (m.count <- m.count + 1; j)
        else probe (i + 1)
    in
    let j = probe 0 in
    Array.unsafe_set m.keys j c;
    Array.unsafe_set m.depths j k;
    Array.unsafe_set m.values j v

  let add m h c k v =
    let size = Array.length m.keys in
    if 2 * m.count >= size && size < max_size then begin
      let keys = m.keys and depths = m.depths and values = m.values in
      let m' = make (2 * size) in
      m.keys <- m'.keys; m.depths <- m'.depths; m.values <- m'.values; m.count <- 0;
      Array.iteri (fun j key ->
          if key != no_key then
            insert m (Constr.hash_bounded key) key depths.(j) values.(j)) keys
    end;
    insert m h c k v
end

(** [expand_constr], with each compound subterm expanded once per binder
    depth, and once for all depths when it expands to itself: the result is
    the same term, and keeps the sharing of [c] where the memo holds it, so
    the cost follows the number of distinct subterms of [c] rather than the
    size of its tree unfolding, which a proof term that shares a subterm many
    times makes exponential. The memo is bounded and lossy: subterms that
    share a [Constr.hash_bounded] value at one depth compete for one run of
    probe slots, and a term with more distinct subterms than the memo holds
    overwrites its own entries, so such a term can still cost its tree
    unfolding. The arms are those of [expand_constr]; a leaf that
    [expand_constr] leaves alone is returned as is. *)
let expand_constr_shared cache modlist top_abst_subst c =
  let share_univs = share_univs cache top_abst_subst in
  let memo = ShareMemo.create () in
  let rec substrec k c =
    match kind c with
    | Rel _ | Sort _ | Meta _ | Int _ | Float _ | String _ -> c
    | Ind (ind,u) ->
      (try share_univs k (IndRef ind) u modlist with Not_found -> c)
    | Construct (cstr,u) ->
      (try share_univs k (ConstructRef cstr) u modlist with Not_found -> c)
    | Const (cst,u) ->
      (try share_univs k (ConstRef cst) u modlist with Not_found -> c)
    | Var id ->
      (try mkRel (find_var k id top_abst_subst) with Not_found -> c)
    | _ ->
      let h = Constr.hash_bounded c in
      match ShareMemo.find memo h c (-1) with
      | Some r -> r
      | None ->
        match ShareMemo.find memo h c k with
        | Some r -> r
        | None ->
          let r = match kind c with
            | Case (ci, u, pms, p, iv, t, br) ->
              begin match share cache top_abst_subst (IndRef ci.ci_ind) modlist with
              | (abstr_uinst, abstr_inst_rel, abstr_inst_length) ->
                let u = Instance.append abstr_uinst u in
                let pms = Array.append (make_inst k abstr_inst_rel) pms in
                let ci = { ci with ci_npar = ci.ci_npar + abstr_inst_length } in
                Constr.map_with_binders succ substrec k (mkCase (ci,u,pms,p,iv,t,br))
              | exception Not_found ->
                Constr.map_with_binders succ substrec k c
              end
            | Proj (p, r, c') ->
              let ind = Names.Projection.inductive p in
              let p' =
                try
                  let exp = share cache top_abst_subst (IndRef ind) modlist in
                  discharge_proj exp p
                with Not_found -> p in
              let c'' = substrec k c' in
              if p == p' && c' == c'' then c else mkProj (p', r, c'')
            | _ -> Constr.map_with_binders succ substrec k c
          in
          (* a term left as is contains nothing the expansion changes, at any
             depth *)
          ShareMemo.add memo h c (if r == c then -1 else k) r;
          r
  in
  if is_empty_modlist modlist && List.is_empty top_abst_subst then c
  else substrec 0 c

(** Cooking is made of 4 steps:
    1. expansion of global constants by applying them to the section
       subcontext they depend on
    2. substitution of named universe variables by de Bruijn universe variables
    3. substitution of named term variables by de Bruijn term variables
    3. generalization of terms over the section subcontext they depend on
       (note that the generalization over universe variable is implicit) *)

(** The main expanding/substitution functions, performing the three first steps *)
let expand_subst0 ?depth cache expand_info abstr_ctx abstr_ausubst c =
  let c = expand_constr ?depth cache expand_info abstr_ctx c in
  let c = Vars.subst_univs_level_constr (make_instance_subst abstr_ausubst) c in
  c

let expand_subst ?depth cache c =
  expand_subst0 ?depth cache.cache cache.info.expand_info cache.info.abstr_info.abstr_ctx cache.info.abstr_info.abstr_ausubst c

(** Adding the final abstraction step, term case *)
let abstract_as_type cache t =
  let ctx = Lazy.force cache.rel_ctx in
  it_mkProd_wo_LetIn (expand_subst cache t) ctx

(** Adding the final abstraction step, type case *)
let abstract_as_body cache c =
  let ctx = Lazy.force cache.rel_ctx in
  it_mkLambda_or_LetIn (expand_subst cache c) ctx

(** Without the final abstraction step, for a subterm under [depth] binders
    of the judgment *)
let expand_subterm cache depth c = expand_subst ~depth cache c

(** [abstract_as_body], with the expansion step computed by
    [expand_constr_shared], so that step keeps the sharing of [c] where the
    memo holds it. The universe substitution that follows it is the one
    [abstract_as_body] does, and in a section with polymorphic universes it
    still walks the tree unfolding. *)
let abstract_as_body_shared cache c =
  let ctx = Lazy.force cache.rel_ctx in
  let info = cache.info in
  let c = expand_constr_shared cache.cache info.expand_info info.abstr_info.abstr_ctx c in
  let c = Vars.subst_univs_level_constr (make_instance_subst info.abstr_info.abstr_ausubst) c in
  it_mkLambda_or_LetIn c ctx

(** Adding the final abstraction step, sort case (for universes) *)
let abstract_as_sort cache s =
  destSort (expand_subst cache (mkSort s))

(** Absorb a named context in the transformation which turns a
    judgment [G, Δ ⊢ ΠΩ.J] into [⊢ ΠG.ΠΔ.((ΠΩ.J)[σ][τ])], that is,
    produces the context [Δ(Ω[σ][τ])] and substitutions [σ'] and [τ]
    that turns a judgment [G, Δ, Ω[σ][τ] ⊢ J] into [⊢ ΠG.ΠΔ.((ΠΩ.J)[σ][τ])]
    via [⊢ ΠG.ΠΔ.Π(Ω[σ][τ]).(J[σ'][τ])] *)
let abstract_named_context expand_info abstr_ausubst hyps =
  let fold decl abstr_ctx =
    let cache = RefTable.create 13 in
    let decl = match decl with
    | NamedDecl.LocalDef (id, b, t) ->
      let id = Context.map_annot_relevance (UVars.subst_sort_level_relevance (make_instance_subst abstr_ausubst)) id in
      let b = expand_subst0 cache expand_info abstr_ctx abstr_ausubst b in
      let t = expand_subst0 cache expand_info abstr_ctx abstr_ausubst t in
      NamedDecl.LocalDef (id, b, t)
    | NamedDecl.LocalAssum (id, t) ->
      let id = Context.map_annot_relevance (UVars.subst_sort_level_relevance (make_instance_subst abstr_ausubst)) id in
      let t = expand_subst0 cache expand_info abstr_ctx abstr_ausubst t in
      NamedDecl.LocalAssum (id, t)
    in
    decl :: abstr_ctx
  in
  Context.Named.fold_outside fold hyps ~init:[]

let create_cache info =
  let cache = RefTable.create 13 in
  let abstr_info = info.abstr_info in
  let named_ctx = lazy (abstract_named_context info.expand_info abstr_info.abstr_ausubst abstr_info.abstr_ctx) in
  let rel_ctx = lazy (List.map NamedDecl.to_rel_decl (Lazy.force named_ctx)) in
  { cache; info; rel_ctx }

(** Turn a named context [Δ] (hyps) and a universe named context
    [G] (uctx) into a rel context and abstract universe context
    respectively; computing also the substitution [σ] and universe
    substitution [τ] such that if [G, Δ ⊢ J] is valid then
    [⊢ ΠG.ΠΔ.(J[σ][τ])] is too, that is, it produces the substitutions
    which turns named binders into de Bruijn binders; computing also
    the instance to apply to take the generalization into account;
    collecting the information needed to do such as a transformation
    of judgment into a [cooking_info] *)
let make_cooking_info ~recursive expand_info hyps uctx =
  let abstr_rev_inst = List.rev (Named.instance_list (fun id -> id) hyps) in
  let abstr_ausubst, abstr_auctx = abstract_universes uctx in
  let abstr_info = { abstr_ctx = hyps; abstr_auctx; abstr_ausubst } in
  let abstr_inst_info = {
    abstr_rev_inst = abstr_rev_inst;
    abstr_uinst = abstr_ausubst;
  } in
  let info = { expand_info; abstr_info } in
  let info = match recursive with
  | None -> info
  | Some ind ->
    let (cmap, imap) = info.expand_info in
    { info with expand_info = (cmap, Mindmap.add ind abstr_inst_info imap) }
  in
  info, abstr_inst_info

let discharges_inductive info =
  not (Mindmap.is_empty (snd info.expand_info))

let names_info info =
  let fold accu id = Id.Set.add (NamedDecl.get_id id) accu in
  List.fold_left fold Id.Set.empty info.abstr_info.abstr_ctx

let rel_context_of_cooking_cache cache =
  Lazy.force cache.rel_ctx

let universe_context_of_cooking_info info =
  info.abstr_info.abstr_auctx

let instance_of_cooking_info info =
  Named.instance mkVar info.abstr_info.abstr_ctx

let instance_of_cooking_cache { info; _ } =
  instance_of_cooking_info info

let discharge_abstract_universe_context abstr auctx =
  (** Given a substitution [abstr.abstr_ausubst := u₀ ... uₙ₋₁] together with an abstract
      context [abstr.abstr_ctx := 0 ... n - 1 |= C{0, ..., n - 1}] of the same length,
      and another abstract context relative to the former context
      [auctx := 0 ... m - 1 |= C'{u₀, ..., uₙ₋₁, 0, ..., m - 1}],
      construct the lifted abstract universe context
      [0 ... n - 1 n ... n + m - 1 |=
        C{0, ... n - 1} ∪
        C'{0, ..., n - 1, n, ..., n + m - 1} ]
      together with the substitution
      [u₀ ↦ Var(0), ... ,uₙ₋₁ ↦ Var(n - 1), Var(0) ↦  Var(n), ..., Var(m - 1) ↦  Var (n + m - 1)].
  *)
  let n = AbstractContext.size abstr.abstr_auctx in
  if (UVars.eq_sizes n (0,0)) then
    (** Optimization: still need to take the union for the constraints between globals *)
    abstr, n, AbstractContext.union abstr.abstr_auctx auctx
  else
    let subst = abstr.abstr_ausubst in
    let suff = UVars.make_abstract_instance auctx in
    let ainst = Instance.append subst suff in
    let substf = make_instance_subst ainst in
    let auctx = UVars.subst_univs_level_abstract_universe_context substf auctx in
    let auctx' = AbstractContext.union abstr.abstr_auctx auctx in
    { abstr with abstr_ausubst = ainst }, n, auctx'

let lift_mono_univs info ctx =
  assert (AbstractContext.is_empty info.abstr_info.abstr_auctx); (* No monorphic constants in a polymorphic section *)
  info, ctx

let lift_poly_univs info auctx =
  (** The constant under consideration is quantified over a
      universe context [auctx]; it has to be quantified further over
      [abstr.abstr_auctx] leading to a new abstraction recipe valid
      under the quantification; that is if we had a judgment
      [G, Δ ⊢ ΠG'.J] to be turned, thanks to [abstr] =
      [{ctx:=Δ;uctx:=G;subst:=σ;usubst:=τ}], into
      [⊢ ΠG.ΠΔ.(ΠG'.J)[σ][τ])], we build the new
      [{ctx:=Δ;uctx:=G(G'[ττ']);subst:=σ;usubst:=ττ'}], for some [τ']
      built by [discharge_abstract_universe_context], that works on
      [J], that is, that allows to turn [GG'[ττ'], Δ ⊢ J] into
      [⊢ ΠG.ΠΔ.(ΠG'.J)[σ][τ]] via [⊢ ΠG(G'[ττ']).ΠΔ.(J[σ][ττ'])] *)
  let abstr_info, n, auctx = discharge_abstract_universe_context info.abstr_info auctx in
  { info with abstr_info }, n, auctx

let lift_private_mono_univs info a =
  let () = assert (AbstractContext.is_empty info.abstr_info.abstr_auctx) in
  let () = assert (Instance.is_empty info.abstr_info.abstr_ausubst) in
  a

let lift_private_poly_univs info (inst, cstrs) =
  let cstrs = UVars.subst_univs_constraints (snd @@ make_instance_subst info.abstr_info.abstr_ausubst) cstrs in
  (inst, cstrs)

let lift_quality info q =
  UVars.subst_sort_level_quality (make_instance_subst info.abstr_info.abstr_ausubst) q

let lift_relevance info relevance =
  UVars.subst_sort_level_relevance (make_instance_subst info.abstr_info.abstr_ausubst) relevance
