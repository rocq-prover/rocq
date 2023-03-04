(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open ModPath
open CErrors
open Util
open Miniml
open Table
open Mlutil

(*S Functions upon ML modules. *)

(** Note: a syntax like [(F M) with ...] is actually legal, see for instance
    bug #4720. Hence the code below tries to handle [MTsig], maybe not in
    a perfect way, but that should be enough for the use of [se_iter] below. *)

let rec msid_of_mt = function
  | MTident mp -> mp
  | MTsig(mp,_) -> mp
  | MTwith(mt,_)-> msid_of_mt mt
  | MTfunsig _ -> assert false (* A functor cannot be inside a MTwith *)

(*s Apply some functions upon all [ml_decl] and [ml_spec] found in a
   [ml_structure]. *)

let mt_iter do_decl do_spec do_mp do_mp_type =
  let rec mt_iter = function
    | MTident mp -> do_mp_type mp
    | MTfunsig (_,mt,mt') -> mt_iter mt; mt_iter mt'
    | MTwith (mt,ML_With_type(idl,l,t))->
        let mp_mt = msid_of_mt mt in
        let l',idl' = List.sep_last idl in
        let mp_w =
          List.fold_left (fun mp l -> MPdot(mp,Label.of_id l)) mp_mt idl'
        in
        let r = GlobRef.ConstRef (Constant.make2 mp_w (Label.of_id l')) in
        mt_iter mt; do_spec (Stype(r,l,Some t))
    | MTwith (mt,ML_With_module(idl,mp))-> mt_iter mt; do_mp mp
    | MTsig (_, sign) -> List.iter spec_iter sign
  and spec_iter = function
    | (_,Spec s) -> do_spec s
    | (_,Smodule mt) -> mt_iter mt
    | (_,Smodtype mt) -> mt_iter mt
  in
  mt_iter

let me_se_iter do_decl do_spec do_mp do_mp_type =
  let rec se_iter = function
    | (_,SEdecl d) -> do_decl d
    | (_,SEmodule (_,m)) ->
        me_iter m.ml_mod_expr; Option.iter (mt_iter do_decl do_spec do_mp do_mp_type) m.ml_mod_type
    | (_,SEmodtype (_,m)) -> mt_iter do_decl do_spec do_mp do_mp_type m
  and me_iter = function
    | MEident mp -> do_mp mp
    | MEfunctor (_,mt,me) -> me_iter me; mt_iter do_decl do_spec do_mp do_mp_type mt
    | MEapply (me,me') -> me_iter me; me_iter me'
    | MEstruct (msid, sel) -> List.iter se_iter sel
  in
  me_iter, se_iter

let me_iter do_decl do_spec do_mp do_mp_type =
  fst (me_se_iter do_decl do_spec do_mp do_mp_type)

let se_iter do_decl do_spec do_mp do_mp_type=
  snd (me_se_iter do_decl do_spec do_mp do_mp_type)

let struct_iter do_decl do_spec do_mp do_mp_type s =
  List.iter
    (function (_,sel) -> List.iter (se_iter do_decl do_spec do_mp do_mp_type) sel) s

(*s Apply some fonctions upon all references in [ml_type], [ml_ast],
  [ml_decl], [ml_spec] and [ml_structure]. *)

type do_ref = GlobRef.t -> unit

let type_iter_references do_type t =
  let rec iter = function
    | Tglob (r,l) -> do_type r; List.iter iter l
    | Tarr (a,b) -> iter a; iter b
    | _ -> ()
  in iter t

let patt_iter_references do_cons p =
  let rec iter = function
    | Pcons (r,l) -> do_cons r; List.iter iter l
    | Pusual r -> do_cons r
    | Ptuple l -> List.iter iter l
    | Prel _ | Pwild -> ()
  in iter p

let ast_iter_references do_term do_cons do_type a =
  let rec iter a =
    ast_iter iter a;
    match a with
      | MLglob r -> do_term r
      | MLcons (_,r,_) -> do_cons r
      | MLcase (ty,_,v) ->
        type_iter_references do_type ty;
        Array.iter (fun (_,p,_) -> patt_iter_references do_cons p) v

      | MLrel _ | MLlam _ | MLapp _ | MLletin _ | MLtuple _ | MLfix _ | MLexn _
      | MLdummy _ | MLaxiom | MLmagic _ | MLuint _ | MLfloat _ | MLparray _ -> ()
  in iter a

let ind_iter_references do_term do_cons do_type kn ind =
  let type_iter = type_iter_references do_type in
  let cons_iter cp l = do_cons (GlobRef.ConstructRef cp); List.iter type_iter l in
  let packet_iter ip p =
    do_type (GlobRef.IndRef ip);
    if lang () == Ocaml then
      (match ind.ind_equiv with
         | Miniml.Equiv kne -> do_type (GlobRef.IndRef (MutInd.make1 kne, snd ip));
         | _ -> ());
    Array.iteri (fun j -> cons_iter (ip,j+1)) p.ip_types
  in
    Array.iteri (fun i -> packet_iter (kn,i)) ind.ind_packets

let decl_iter_references do_term do_cons do_type =
  let type_iter = type_iter_references do_type
  and ast_iter = ast_iter_references do_term do_cons do_type in
  function
    | Dind (kn,ind) -> ind_iter_references do_term do_cons do_type kn ind
    | Dtype (r,_,t) -> do_type r; type_iter t
    | Dterm (r,a,t) -> do_term r; ast_iter a; type_iter t
    | Dfix(rv,c,t) ->
        Array.iter do_term rv; Array.iter ast_iter c; Array.iter type_iter t

let spec_iter_references do_term do_cons do_type = function
  | Sind (kn,ind) -> ind_iter_references do_term do_cons do_type kn ind
  | Stype (r,_,ot) -> do_type r; Option.iter (type_iter_references do_type) ot
  | Sval (r,t) -> do_term r; type_iter_references do_type t

(*s Searching occurrences of a particular term (no lifting done). *)

exception Found

let rec ast_search f a =
  if f a then raise Found else ast_iter (ast_search f) a

let decl_ast_search f = function
  | Dterm (_,a,_) -> ast_search f a
  | Dfix (_,c,_) -> Array.iter (ast_search f) c
  | _ -> ()

let struct_ast_search f s =
  try struct_iter (decl_ast_search f) (fun _ -> ()) (fun _ -> ()) (fun _ -> ()) s; false
  with Found -> true

let rec type_search f = function
  | Tarr (a,b) -> type_search f a; type_search f b
  | Tglob (r,l) -> List.iter (type_search f) l
  | u -> if f u then raise Found

let decl_type_search f = function
  | Dind (_,{ind_packets=p})  ->
      Array.iter
        (fun {ip_types=v} -> Array.iter (List.iter (type_search f)) v) p
  | Dterm (_,_,u) -> type_search f u
  | Dfix (_,_,v) -> Array.iter (type_search f) v
  | Dtype (_,_,u) -> type_search f u

let spec_type_search f = function
  | Sind (_,{ind_packets=p}) ->
      Array.iter
        (fun {ip_types=v} -> Array.iter (List.iter (type_search f)) v) p
  | Stype (_,_,ot) -> Option.iter (type_search f) ot
  | Sval (_,u) -> type_search f u

let struct_type_search f s =
  try
    struct_iter (decl_type_search f) (spec_type_search f) (fun _ -> ()) (fun _ -> ()) s;
    false
  with Found -> true


(*s Generating the signature. *)

let rec msig_of_ms = function
  | [] -> []
  | (l,SEdecl (Dind (kn,i))) :: ms ->
      (l,Spec (Sind (kn,i))) :: (msig_of_ms ms)
  | (l,SEdecl (Dterm (r,_,t))) :: ms ->
      (l,Spec (Sval (r,t))) :: (msig_of_ms ms)
  | (l,SEdecl (Dtype (r,v,t))) :: ms ->
      (l,Spec (Stype (r,v,Some t))) :: (msig_of_ms ms)
  | (l,SEdecl (Dfix (rv,bv,tv))) :: ms ->
      let msig = ref (msig_of_ms ms) in
      for i = Array.length rv - 1 downto 0 do
        match bv.(i) with
        | MLexn "UNUSED" -> ()
        | _ -> msig := (l,Spec (Sval (rv.(i),tv.(i))))::!msig
      done;
      !msig
  | (l,SEmodule (mp,m)) :: ms ->
    let m = match m.ml_mod_type with
      | None -> mtyp_of_mexpr m.ml_mod_expr
      | Some m -> m
    in
    (l,Smodule m) :: (msig_of_ms ms)
  | (l,SEmodtype (_,m)) :: ms -> (l,Smodtype m) :: (msig_of_ms ms)

and mtyp_of_mexpr = function
  | MEfunctor (id,ty,e) -> MTfunsig (id,ty, mtyp_of_mexpr e)
  | MEstruct (mp,str) -> MTsig (mp, msig_of_ms str)
  | _ -> assert false

let signature_of_structure s =
  List.map (fun (mp,ms) -> mp,msig_of_ms ms) s

(*s Searching one [ml_decl] in a [ml_structure] by its [global_reference] *)

let is_modular = function
  | SEdecl _ -> false
  | SEmodule _ | SEmodtype _ -> true

let rec search_structure l m = function
  | [] -> raise Not_found
  | (lab,d)::_ when Label.equal lab l && (is_modular d : bool) == m -> d
  | _::fields -> search_structure l m fields

let get_decl_in_structure r struc =
  try
    let base_mp,ll = labels_of_ref r in
    if not (at_toplevel base_mp) then error_not_visible r;
    let sel = List.assoc_f ModPath.equal base_mp struc in
    let rec go ll sel = match ll with
      | [] -> assert false
      | l :: ll ->
          match search_structure l (not (List.is_empty ll)) sel with
            | SEdecl d -> d
            | SEmodtype (_,m) -> assert false
            | SEmodule (_,m) ->
                let rec aux = function
                  | MEstruct (_,sel) -> go ll sel
                  | MEfunctor (_,_,sel) -> aux sel
                  | MEident _ | MEapply _ -> error_not_visible r
                in aux m.ml_mod_expr

    in go ll sel
  with Not_found ->
    anomaly (Pp.str "reference not found in extracted structure.")


(*s Optimization of a [ml_structure]. *)

(* Some transformations of ML terms. [optimize_struct] simplify
   all beta redexes (when the argument does not occur, it is just
   thrown away; when it occurs exactly once it is substituted; otherwise
   a let-in redex is created for clarity) and iota redexes, plus some other
   optimizations. *)

let dfix_to_mlfix rv av i =
  let rec make_subst n s =
    if n < 0 then s
    else make_subst (n-1) (Refmap'.add rv.(n) (n+1) s)
  in
  let s = make_subst (Array.length rv - 1) Refmap'.empty
  in
  let rec subst n t = match t with
    | MLglob ((GlobRef.ConstRef kn) as refe) ->
        (try MLrel (n + (Refmap'.find refe s)) with Not_found -> t)
    | _ -> ast_map_lift subst n t
  in
  let ids = Array.map (fun r -> Label.to_id (label_of_r r)) rv in
  let c = Array.map (subst 0) av
  in MLfix(i, ids, c)

(* [optim_se] applies the [normalize] function everywhere and does the
   inlining of code. The inlined functions are kept for the moment in
   order to preserve the global interface, later [depcheck_se] will get
   rid of them if possible *)

let rec optim_se to_appear s = function
  | [] -> []
  | (l,SEdecl (Dterm (r,a,t))) :: lse ->
      let a = normalize (ast_glob_subst !s a) in
      let i = inline r a in
      if i then s := Refmap'.add r a !s;
      let d = match dump_unused_vars (optimize_fix a) with
        | MLfix (0, _, [|c|]) ->
          Dfix ([|r|], [|ast_subst (MLglob r) c|], [|t|])
        | a -> Dterm (r, a, t)
      in
      (l,SEdecl d) :: (optim_se to_appear s lse)
  | (l,SEdecl (Dfix (rv,av,tv))) :: lse ->
      let av = Array.map (fun a -> normalize (ast_glob_subst !s a)) av in
      (* This fake body ensures that no fixpoint will be auto-inlined. *)
      let fake_body = MLfix (0,[||],[||]) in
      for i = 0 to Array.length rv - 1 do
        if inline rv.(i) fake_body
        then s := Refmap'.add rv.(i) (dfix_to_mlfix rv av i) !s
      done;
      let av' = Array.map dump_unused_vars av in
      (l,SEdecl (Dfix (rv, av', tv))) :: (optim_se to_appear s lse)
  | (l,SEmodule (mp,m)) :: lse ->
      let m = { m with ml_mod_expr = optim_me to_appear s m.ml_mod_expr}
      in (l,SEmodule (mp,m)) :: (optim_se to_appear s lse)
  | se :: lse -> se :: (optim_se to_appear s lse)

and optim_me to_appear s = function
  | MEstruct (msid, lse) -> MEstruct (msid, optim_se to_appear s lse)
  | MEident mp as me -> me
  | MEapply (me, me') ->
      MEapply (optim_me to_appear s me, optim_me to_appear s me')
  | MEfunctor (mbid,mt,me) -> MEfunctor (mbid,mt, optim_me to_appear s me)

(* After these optimisations, some dependencies may not be needed anymore.
   For non-library extraction, we recompute a minimal set of dependencies
   for first-level definitions (no module pruning yet). *)

let base_r = let open GlobRef in function
  | ConstRef c as r -> r
  | IndRef (kn,_) -> IndRef (kn,0)
  | ConstructRef ((kn,_),_) -> IndRef (kn,0)
  | _ -> assert false

(* Modules on the contents of which there is some dependency *)
let reset_needed_mp, add_needed_mp, is_needed_mp =
  let needed_mps = ref MPset.empty in
  ((fun () -> needed_mps := MPset.empty),
   (fun mp -> needed_mps := MPset.union (prefixes_mp mp) !needed_mps),
   (fun mp -> MPset.mem mp !needed_mps))

(* Modules to be fully extracted *)
let reset_needed_mp_full, add_needed_mp_full, is_needed_mp_full =
  let needed_mps_full = ref MPset.empty in
  ((fun () -> needed_mps_full := MPset.empty),
   (fun mp -> needed_mps_full := MPset.add mp !needed_mps_full; add_needed_mp mp),
   (fun mp -> MPset.mem mp !needed_mps_full))

(* Dependencies on module types *)
let reset_needed_mp_type, add_needed_mp_type, is_needed_mp_type =
  let needed_mps_type = ref MPset.empty in
  ((fun () -> needed_mps_type := MPset.empty),
   (fun mp -> needed_mps_type := MPset.add mp !needed_mps_type; add_needed_mp mp),
   (fun mp -> MPset.mem mp !needed_mps_type || is_needed_mp_full mp))

(* Dependencies on a global reference *)
let reset_needed, add_needed, found_needed, is_needed =
  let needed = ref Refset'.empty in
  ((fun () -> needed := Refset'.empty),
   (fun r -> needed := Refset'.add (base_r r) !needed; add_needed_mp (modpath_of_r r)),
   (fun r -> needed := Refset'.remove (base_r r) !needed),
   (fun r ->
     let r = base_r r in
     Refset'.mem r !needed || is_needed_mp_full (modpath_of_r r)))

let reset_needed_all () =
  reset_needed_mp_full ();
  reset_needed_mp ();
  reset_needed_mp_type ();
  reset_needed ()

let declared_refs = function
  | Dind (kn,_) -> [GlobRef.IndRef (kn,0)]
  | Dtype (r,_,_) -> [r]
  | Dterm (r,_,_) -> [r]
  | Dfix (rv,_,_) -> Array.to_list rv

(* Computes the dependencies of a declaration, except in case
   of custom extraction. *)

let compute_deps_decl = function
  | Dind (kn,ind) ->
      (* Todo Later : avoid dependencies when Extract Inductive *)
      ind_iter_references add_needed add_needed add_needed kn ind
  | Dtype (r,ids,t) ->
      if not (is_custom r) then type_iter_references add_needed t
  | Dterm (r,u,t) ->
      type_iter_references add_needed t;
      if not (is_custom r) then
        ast_iter_references add_needed add_needed add_needed u
  | Dfix _ as d ->
      decl_iter_references add_needed add_needed add_needed d

let compute_deps_spec = function
  | Sind (kn,ind) ->
      (* Todo Later : avoid dependencies when Extract Inductive *)
      ind_iter_references add_needed add_needed add_needed kn ind
  | Stype (r,ids,t) ->
      if not (is_custom r) then Option.iter (type_iter_references add_needed) t
  | Sval (r,t) ->
      type_iter_references add_needed t

let depcheck_me_iter =
  me_iter compute_deps_decl compute_deps_spec add_needed_mp_full add_needed_mp_type

let depcheck_mt_iter =
  mt_iter compute_deps_decl compute_deps_spec add_needed_mp_full add_needed_mp_type

let rec depcheck_se_list = function
  | [] -> []
  | t :: se ->
    let se' = depcheck_se_list se in
    match depcheck_se t with
    | None -> se'
    | Some t' -> t' :: se'

and depcheck_se = function
  | (l,SEdecl d) as t ->
    let refs = declared_refs d in
    let refs' = List.filter is_needed refs in
    if List.is_empty refs' then
      (List.iter remove_info_axiom refs;
       List.iter remove_opaque refs;
       None)
    else begin
      List.iter found_needed refs';
      (* Hack to avoid extracting unused part of a Dfix *)
      match d with
        | Dfix (rv,trms,tys) when (List.for_all is_custom refs') ->
          let trms' = Array.map2 (fun r v -> if List.mem r refs' then v else MLexn "UNUSED") rv trms in
          Some (l, SEdecl (Dfix (rv,trms',tys)))
        | _ -> (compute_deps_decl d; Some t)
    end
  | (l,SEmodule (mp,m)) ->
    if is_needed_mp mp then
      let mt = m.ml_mod_type in
      (match mt with
       | Some mt -> add_needed_mp_full mp; depcheck_mt_iter mt
       | None -> ());
      let m' = depcheck_me m.ml_mod_expr in
      Some (l,SEmodule (mp,{ml_mod_expr = m'; ml_mod_type = mt}))
    else
      None
  | (l,SEmodtype (mp,mt)) as t ->
    if is_needed_mp_type mp then
      (depcheck_mt_iter mt;
       Some t)
    else
      None

and depcheck_me = function
  | MEident mp as t -> add_needed_mp mp; t
  | MEfunctor (mbid,mt,me) as m ->
    depcheck_mt_iter mt;
    depcheck_me_iter me;
    m
  | MEapply (me,me') as m -> depcheck_me_iter me; depcheck_me_iter me'; m
  | MEstruct (msid, sel) -> MEstruct (msid, depcheck_se_list sel)

let rec depcheck_struct = function
  | [] -> []
  | (mp,lse)::struc ->
      let struc' = depcheck_struct struc in
      let lse' = depcheck_se_list lse in
      if List.is_empty lse' then struc' else (mp,lse')::struc'

exception RemainingImplicit of kill_reason

let check_for_remaining_implicits struc =
  let check = function
    | MLdummy (Kimplicit _ as k) -> raise (RemainingImplicit k)
    | _ -> false
  in
  try ignore (struct_ast_search check struc)
  with RemainingImplicit k -> err_or_warn_remaining_implicit k

let optimize_struct to_appear struc =
  let subst = ref (Refmap'.empty : ml_ast Refmap'.t) in
  let opt_struc =
    List.map (fun (mp,lse) -> (mp, optim_se (fst to_appear) subst lse))
      struc
  in
  let mini_struc =
    if library () then
      List.filter (fun (_,lse) -> not (List.is_empty lse)) opt_struc
    else
      begin
        reset_needed_all ();
        List.iter add_needed (fst to_appear);
        List.iter add_needed_mp_full (snd to_appear);
        depcheck_struct opt_struc
      end
  in
  let () = check_for_remaining_implicits mini_struc in
  mini_struc
