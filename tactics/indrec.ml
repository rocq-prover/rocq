(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open CErrors
open Util
open Names
open Constr
open EConstr
open Declarations
open Context
open Inductive
open Environ
open LibBinding
open State
open AllScheme
open Retyping

type dep_flag = bool

(* Errors related to recursors building *)
type recursion_scheme_error =
  | NotMutualInScheme of inductive * inductive
  | DuplicateInductiveBlock of inductive

exception RecursionSchemeError of env * recursion_scheme_error

let (let@) x f = x f
let (let*) x f = State.bind x f
let dbg = CDebug.create ~name:"generate_eliminators" ()

(* ************************************************************************** *)
(*                          Functions on Parameters                           *)
(* ************************************************************************** *)

let split_uparans_nuparams mib params =
  let (uparams, nuparams) = Context.Rel.chop_nhyps mib.mind_nparams_rec (List.rev params) in
  (List.rev uparams, List.rev nuparams)

(** Generalize parameters for template and univ poly, and split uniform and non-uniform parameters *)
let get_params_sep sigma mib u =
  let (sigma, params, _) = Inductiveops.paramdecls_fresh_template sigma (mib, u) in
  let (uparams, nuparams) = split_uparans_nuparams mib params in
  (sigma, uparams, nuparams)

(** Closure of uniform parameters forgetting letins *)
let closure_uparams binder naming_scheme uparams cc =
  closure_context fid binder Old naming_scheme uparams cc

(** Closure of non-uniform parameters if [b], forgetting letins  *)
let closure_nuparams_opt ~quantify binder naming_scheme nuparams cc =
    if quantify
    then closure_context fid binder Old naming_scheme nuparams (fun x -> cc (Some x))
    else cc None

(** Closure of non-uniform parameters if [key_uparams_opt = None], forgetting letins  *)
let closure_nuparams binder naming_scheme nuparams key_uparams_opt cc =
  let@ key_uparams_opt' = closure_nuparams_opt ~quantify:(Option.is_empty key_uparams_opt)
                            binder naming_scheme nuparams in
  match key_uparams_opt, key_uparams_opt' with
  | Some z, None | None, Some z -> cc z
  | _, _ -> assert false

(** Get the position in ind_bodies out of the position of mind_packets *)
let find_opt_pos p l =
  let rec aux i l =
    match l with
    | [] -> None
    | h::_ when p h -> Some (i, h)
    | _::t -> aux (1+i) t
  in
  aux 0 l

(** Closure for indices. They are considered as [Fresh] as they are not in the context of the arguments *)
let closure_indices binder naming_scheme indb u f =
  let* i = get_indices indb u in
  closure_context fid binder Fresh naming_scheme i f


(* ************************************************************************** *)
(*                         Generate Eliminators' Type                         *)
(* ************************************************************************** *)

(* Convention for comments:
  - A1 ... An : uniform parameters = uparams
  - B0 ... Bm : non-uniform parameters = nuparams
  - i0 ... il : indices
*)

(** Builds the type of the predicate for the i-th block
    forall (B0 ... Bm : nuparams),
    forall (i1 ... tl : indices),
    (Ind A1 ... An B0 ... Bm i1 ... il) -> U)  *)
let make_type_pred kn u (pos_ind, ind, dep, sort) key_uparams nuparams key_nuparams_opt =
  let@ key_nuparams = closure_nuparams Prod naming_hd_fresh nuparams key_nuparams_opt in
  let@ key_indices = closure_indices  Prod (naming_hd_fresh_dep dep) ind u in
  (* NOT DEP: return the sort *)
  if not dep then
    return @@ mkSort sort
  else
    (* DEP: bind the inductive, and return the sort *)
    let* ind_rev = ind_relevance ind u in
    let ind_name = make_annot Anonymous ind_rev in
    let* tind = make_ind ((kn, pos_ind), u) key_uparams key_nuparams key_indices in
    let@ _ = make_binder fid Prod naming_hd_fresh ind_name tind in
    return @@ mkSort sort

 (** Make the predicate P B0 ... Bm i0 ... il t *)
let make_pred rec_hyp key_preds focus dep inst_nuparams inst_indices t =
  let* pred_var = geti_term key_preds focus in
  let pred =
    if rec_hyp
    then mkApp (pred_var, Array.concat [inst_nuparams; inst_indices])
    else mkApp (pred_var, inst_indices) in
  if not dep
  then return pred
  else return @@ mkApp (pred, [| t |])

(** Closure Predicates *)
let closure_preds kn u ind_bodies binder key_uparams nuparams key_nuparams_opt cc =
  fold_right_state (fun a l -> a :: l) ind_bodies (fun _ ind cc ->
    let pred_name = make_annot (Name (Id.of_string "P")) ERelevance.relevant in
    let* pred_type = make_type_pred kn u ind key_uparams nuparams key_nuparams_opt in
    make_binder fid binder naming_hd_fresh pred_name pred_type cc
  ) cc

(** Recursively compute the predicate, returns [None] if it is not nested *)
let compute_pred to_compute f i x =
  if to_compute then
    let* (locs, head) = decompose_lambda_decls x in
    let@ key_loc = closure_context fopt Lambda Fresh naming_id locs in
    (* create new variable *)
    let* head_sort = retyping_sort_of head in
    let arg_rev = relevance_of_sort head_sort in
    let arg_name = make_annot Anonymous arg_rev in
    (* let name_var = make_annot Anonymous ERelevance.relevant in *)
    let@ key_arg = make_binder fopt Lambda naming_id arg_name head in
    let* arg_type = State.get_type key_arg in
    (* compute rec call *)
    let* res = f key_arg arg_type in
    return @@ res
else return None

(** Recursively compute the predicate, returns [None] if it is not nested *)
let compute_pred_eta to_compute f i x =
  let* res = compute_pred to_compute f i x in
  let* sigma = get_sigma in
  let res = Option.map (Reductionops.shrink_eta sigma) res in
  return res

(** Compute the type of the recursive call *)
let rec make_rec_call_hyp kn pos_ind mib ind_bodies key_preds key_arg arg_type =
  (* Decompose the argument, rebind local variables and compute the argument *)
  let* (locs, head) = view_argument kn mib [] [] arg_type in
  let@ key_locals = closure_context fopt Prod Fresh naming_id locs in
  let* arg_term = get_term key_arg in
  let* locs_term = get_terms key_locals in
  let inst_arg = mkApp (arg_term, locs_term) in
  (* Match head *)
  match head with
  | ArgIsInd (pos_ind_block, inst_nuparams, inst_indices) ->
    begin
      (* generate recursion hypotheses only for the blocks that are used *)
      match find_opt_pos (fun (i,_,_,_) -> i = pos_ind_block) ind_bodies with
      | None -> return None
      | Some (pred_pos, (_, _, pred_dep, sort)) ->
          let* rec_hyp = make_pred true key_preds pred_pos pred_dep inst_nuparams inst_indices inst_arg in
          return (Some (rec_hyp))
    end
  | ArgIsNested (kn_nested, pos_nested, mib_nested, mib_nested_strpos, ind_nested,
                  inst_uparams, inst_nuparams_indices) ->
      (* eta expand arguments *)
      let uparams_nested = of_rel_context @@ fst @@
                split_uparans_nuparams mib_nested mib_nested.mind_params_ctxt in
      let* inst_uparams = eta_expand_instantiation inst_uparams uparams_nested in
      (* Compute the recursive predicates *)
      let compute_pred i x b = compute_pred_eta b (make_rec_call_hyp kn pos_ind mib ind_bodies key_preds) i x in
      let* rec_preds = array_map2i compute_pred inst_uparams (Array.of_list mib_nested_strpos) in
      (* If at least one argument is nested, lookup the sparse parametricity *)
      let args_are_nested = Array.map Option.has_some rec_preds in
      if Array.for_all not args_are_nested then
        return None
      else begin
        match lookup_all_theorem (kn, pos_ind) (kn_nested, pos_nested) (Array.to_list args_are_nested) with
        | None -> return None
        | Some (partial_nesting, ref_pred, _) ->
          let* rec_hyp = make_all_predicate ~partial_nesting ref_pred mib_nested_strpos
                          inst_uparams rec_preds inst_nuparams_indices inst_arg in
          (* return *)
          return (Some (rec_hyp))
      end
  | _ -> return None

(** Create and bind the recursive call, if [rec_hyp] and if any *)
let make_rec_call_cc rec_hyp kn pos_ind mib ind_bodies key_preds _ key_arg cc =
  let* arg = State.get_type key_arg in
  if rec_hyp then begin
    let* rec_call = make_rec_call_hyp kn pos_ind mib ind_bodies key_preds key_arg arg in
    match rec_call with
    | None -> cc [key_arg]
    | Some rec_hyp_type ->
      (* Compute the relevance after the instantiation *)
      let* rec_hyp_sort = retyping_sort_of rec_hyp_type in
      let rec_hyp_rev = relevance_of_sort rec_hyp_sort in
      let rec_hyp_name = make_annot Anonymous rec_hyp_rev in
      let@ _ = make_binder fid Prod naming_id rec_hyp_name rec_hyp_type in
      cc [key_arg]
    end
  else cc [key_arg]

(** Closure of the args, and of the rec call if [rec_hyp], and if any *)
let closure_args_and_rec_call rec_hyp kn pos_ind u mib ind_bodies dep key_preds args =
  read_by_decl args
    (build_binder fid Prod Old (naming_hd_dep dep))
    (fun _ _ cc -> cc [])
    (make_rec_call_cc rec_hyp kn pos_ind mib ind_bodies key_preds)

(** Generates the type associated to a constructor
    forall (B0 ... Bm : nuparams),
    forall x0 : arg0, [P x0], ..., xn : argn, [P n],
    P B0 ... Bm f0 ... fl (cst A0 ... An B0 ... Bm x0 ... xl) *)
let make_type_ctor kn u mib ind_bodies pos_list (pos_ind, ind, dep, sort)
    pos_ctor (args, indices) key_uparams nuparams key_nuparams_opt key_preds =
  let rec_hyp = Option.is_empty key_nuparams_opt in
  let@ key_nuparams = closure_nuparams Prod naming_id nuparams key_nuparams_opt in
  let@ key_args = closure_args_and_rec_call rec_hyp kn pos_ind u mib ind_bodies dep key_preds args in
  (* make cst *)
  let* cst_args = get_terms key_args in
  let* cst = make_cst ((kn, pos_ind), u) pos_ctor key_uparams key_nuparams cst_args in
  (* make pred cst *)
  let* inst_nuparams = get_terms key_nuparams in
  let* inst_indices = array_mapi (fun _ -> weaken) indices in
  make_pred rec_hyp key_preds pos_list dep inst_nuparams inst_indices cst

(** Closure assumptions functions over all the ctors *)
let closure_ctors rec_hyp kn mib u ind_bodies binder key_uparams nuparams key_nuparams_opt key_preds =
  fold_right_state (fun a l -> a :: l) ind_bodies (
    fun pos_list (pos_ind, ind, dep, sort) cc ->
    iterate_ctors mib ind u (
      fun pos_ctor ctor cc ->
      let assum_name = make_annot (Name ind.mind_consnames.(pos_ctor)) (relevance_of_sort sort) in
      let* assum_type = make_type_ctor kn u mib ind_bodies pos_list (pos_ind, ind, dep, sort)
                    pos_ctor ctor key_uparams nuparams key_nuparams_opt key_preds in
      make_binder fid binder naming_hd_fresh assum_name assum_type cc
    ) cc
  )

(** Make the type of the conclusion
    P B0 ... Bm i0 ... il x *)
let make_ccl rec_hyp key_preds focus dep key_nuparams key_indices key_VarMatch =
  let* inst_nuparams = get_terms key_nuparams in
  let* inst_indices = get_terms key_indices in
  let* var = get_term key_VarMatch in
  make_pred rec_hyp key_preds focus dep inst_nuparams inst_indices var


(** Make the return type
    forall (B0 ... Bm : nuparams),
    forall (i1 ... il : indices),
    forall (x : Ind A0 ... An B0 ... Bm i0 ... il),
    P B0 ... Bm i0 ... il x *)
let make_return_type kn u ind_bodies focus key_uparams nuparams key_nuparams_opt key_preds =
  let (pos_ind, ind, dep, sort) = List.nth ind_bodies focus in
  let@ key_nuparams = closure_nuparams Prod naming_hd_fresh nuparams key_nuparams_opt in
  let@ key_indices = closure_indices Prod naming_hd_fresh ind u in
  let* ind_rev = ind_relevance ind u in
  let ind_name = make_annot Anonymous ind_rev in
  let* ind_tm = make_ind ((kn, pos_ind), u) key_uparams key_nuparams key_indices in
  let@ (key_VarMatch) = make_binder fid Prod naming_hd_fresh ind_name ind_tm in
  let rec_hyp = Option.is_empty key_nuparams_opt in
  make_ccl rec_hyp key_preds focus dep key_nuparams key_indices key_VarMatch

(** Generate the type of the recursor *)
let gen_elim_type print_constr rec_hyp kn u mib uparams nuparams ind_bodies focus =
  let t =
    let@ key_uparams = closure_uparams Prod naming_hd_fresh uparams in
    let@ key_nuparams_opt = closure_nuparams_opt ~quantify:(not rec_hyp) Prod naming_hd_fresh nuparams in
    let@ key_preds = closure_preds kn u ind_bodies Prod key_uparams nuparams key_nuparams_opt in
    let@ key_ctors = closure_ctors rec_hyp kn mib u ind_bodies Prod key_uparams nuparams key_nuparams_opt key_preds in
    make_return_type kn u ind_bodies focus key_uparams nuparams key_nuparams_opt key_preds
  in
  (* DEBUG *)
  let* t = t in
  let* env = get_env in
  let* sigma = get_sigma in
  dbg Pp.(fun () ->
        str "Eliminator's Type for "
    ++ str "(" ++ str (MutInd.to_string kn) ++ str ", " ++ int focus  ++ str ") "
    ++ (
      if rec_hyp then
        str "with induction hypotheses"
      else
        str "without induction hypotheses"
      )
    ++ fnl () ++ print_constr env sigma t ++ fnl ()
    );
  return t


(* ************************************************************************** *)
(*                         Generate Eliminators' Body                         *)
(* ************************************************************************** *)

(** Compute the recursive call *)
let rec make_rec_call_proof kn pos_ind mib ind_bodies key_preds key_fixs key_arg arg_type =
  (* Decompose the argument, rebind local variables and compute the argument *)
  let* (locs, head) = view_argument kn mib [] [] arg_type in
  let@ key_locals = closure_context fopt Lambda Fresh naming_id locs in
  let* arg_term = get_term key_arg in
  let* locs_term = get_terms key_locals in
  let inst_arg = mkApp (arg_term, locs_term) in
  (* Match head *)
  match head with
  | ArgIsInd (pos_ind_block, inst_nuparams, inst_indices) ->
    begin
    (* generate recursion hypotheses only for the blocks that are used *)
      match find_opt_pos (fun (i,_,_,_) -> i = pos_ind_block) ind_bodies with
      | None -> return None
      | Some (pred_pos, _) ->
        (* Fi B0 ... Bm i0 ... il (x a0 ... an) *)
        let* fix = geti_term key_fixs pred_pos in
        return @@ Some (mkApp (fix, Array.concat [inst_nuparams; inst_indices; [|inst_arg|]]))
    end
  | ArgIsNested (kn_nested, pos_nested, mib_nested, mib_nested_strpos, ind_nested,
                  inst_uparams, inst_nuparams_indices) ->
      (* eta expand arguments *)
      let uparams_nested = of_rel_context @@ fst @@
              split_uparans_nuparams mib_nested mib_nested.mind_params_ctxt in
      let* inst_uparams = eta_expand_instantiation inst_uparams uparams_nested in
      (* Compute the recursive predicates, and their proofs *)
      let compute_pred_preds i x b = compute_pred_eta b (make_rec_call_hyp kn pos_ind mib ind_bodies key_preds) i x in
      let* rec_preds = array_map2i compute_pred_preds inst_uparams (Array.of_list mib_nested_strpos) in
      let compute_pred_holds i x b = compute_pred_eta b (make_rec_call_proof kn pos_ind mib ind_bodies key_preds key_fixs) i x in
      let* rec_preds_hold = array_map2i compute_pred_holds inst_uparams (Array.of_list mib_nested_strpos) in
      (* If at least one argument is nested, lookup the local fundamental theorem *)
      let args_are_nested = Array.map Option.has_some rec_preds_hold in
      if Array.for_all not args_are_nested then
        return None
      else begin
        match lookup_all_theorem (kn, pos_ind) (kn_nested, pos_nested) (Array.to_list args_are_nested) with
        | None -> return None
        | Some (partial_nesting, _, ref_thm) ->
          let* rec_hyp = make_all_theorem ~partial_nesting ref_thm mib_nested_strpos inst_uparams
                          rec_preds rec_preds_hold inst_nuparams_indices inst_arg in
          return @@ Some rec_hyp
      end
  | _ -> return None

(** Compute the arguments of the rec call *)
let compute_args_fix rec_hyp kn pos_ind mib ind_bodies pos_list key_preds key_fixs key_args =
  CList.fold_right_i (fun pos_arg key_arg acc ->
    let* acc = acc in
    let* arg_term = get_term key_arg in
    if rec_hyp then
      let* arg_type = State.get_type key_arg in
      let* rec_call = make_rec_call_proof kn pos_ind mib ind_bodies key_preds key_fixs key_arg arg_type in
      match rec_call with
        | Some rc_tm -> return @@ arg_term :: rc_tm :: acc
        | None -> return @@ arg_term :: acc
    else
      return @@ arg_term :: acc
  ) 0 key_args (return [])

let gen_elim_term print_constr rec_hyp kn u mib uparams nuparams ind_bodies focus =

  let t =

  (* 1. Closure Uparams / preds / ctors *)
  let@ key_uparams = closure_uparams Lambda naming_hd_fresh uparams in
  let@ key_nuparams_opt = closure_nuparams_opt ~quantify:(not rec_hyp) Lambda naming_hd_fresh nuparams in
  let@ key_preds = closure_preds kn u ind_bodies Lambda key_uparams nuparams key_nuparams_opt in
  let@ key_ctors = closure_ctors rec_hyp kn mib u ind_bodies Lambda key_uparams nuparams key_nuparams_opt key_preds in
  (* 2. Fixpoint *)
  let fix_name pos_list (_,_,_,sort) = make_annot (Name (Id.of_string "F")) (relevance_of_sort sort) in
  let fix_type pos_list _ = make_return_type kn u ind_bodies pos_list key_uparams nuparams key_nuparams_opt key_preds in
  let fix_rarg pos_list (_,ind,_,_) = (mib.mind_nparams - mib.mind_nparams_rec) + ind.mind_nrealargs in
  let is_rec =
    let (_, ind, _, _) = List.hd ind_bodies in
    List.length ind_bodies > 1 || (rec_hyp && Inductiveops.mis_is_recursive ind) in
  let@ (key_fixs, pos_list, (pos_ind, ind, dep, sort)) =
    (* Doe not create a fix if it is not-recursive and only has one inductive body *)
    if is_rec
    then make_fix ind_bodies focus fix_rarg fix_name fix_type
    else fun cc -> cc ([], 0, List.hd ind_bodies) in
  (* 3. Closure Nuparams / Indices / Var *)
  let@ key_nuparams = closure_nuparams Lambda naming_hd_fresh nuparams key_nuparams_opt in
  let@ key_indices = closure_indices Lambda naming_hd_fresh ind u in
  let* ind_rev = ind_relevance ind u in
  let ind_name = make_annot Anonymous ind_rev in
  let* tind = make_ind ((kn, pos_ind), u) key_uparams key_nuparams key_indices in
  let@ key_VarMatch = make_binder fid Lambda naming_hd_fresh ind_name tind in
  let ccl =
  (* 4 Match to prove P ... x *)
    let* inst_params = get_terms (key_uparams @ key_nuparams )in
    let case_pred = make_ccl rec_hyp key_preds pos_list dep key_nuparams in
    let* var_match = get_term key_VarMatch in
    let* inst_indices = get_terms key_indices in
    let@ (key_args, _, _, pos_ctor) =
      make_case_or_projections naming_hd_fresh mib (kn, pos_ind) ind u key_uparams key_nuparams inst_params
        inst_indices case_pred (relevance_of_sort sort) var_match in
    (* 5 Body of the branch *)
    let* hyp = getij_term key_ctors pos_list pos_ctor in
    let* inst_nuparams = get_terms key_nuparams in
    let* cfix = compute_args_fix rec_hyp kn pos_ind mib ind_bodies pos_list key_preds key_fixs key_args in
    if is_rec then
      typing_checked_appvect hyp (Array.concat [inst_nuparams; Array.of_list cfix])
    else
      typing_checked_appvect hyp (Array.of_list cfix)
  in
    (* 6. If it is not-recursive, has primitive projections and is dependent => add a cast *)
    let* env = get_env in
    let projs = Environ.get_projections env (kn, pos_ind) in
  if is_rec || Option.is_empty projs || not dep then
    ccl
  else
    let* arg_type = make_ccl rec_hyp key_preds pos_list dep key_nuparams key_indices key_VarMatch in
    let* ccl = ccl in
    return @@ mkCast (ccl, DEFAULTcast, arg_type)

  in
  (* DEBUG *)
  let* t = t in
  let* env = get_env in
  let* sigma = get_sigma in
    dbg Pp.(fun () ->
      str "Eliminator's for "
      ++ str "(" ++ str (MutInd.to_string kn) ++ str ", " ++ int focus  ++ str ") "
      ++ (
        if rec_hyp then
          str "with induction hypotheses"
        else
          str "without induction hypotheses"
        )
      ++ fnl () ++ print_constr env sigma t ++ fnl ()
    );
  return t

(**********************************************************************)
(* build the eliminators mutual and individual *)

(** Check all dependent eliminations are allowed *)
let check_valid_elimination env sigma (kn, n) mib u lrecspec rec_hyp =
  (* Check the mutual can be eliminated. *)
  if mib.mind_private = Some true
  then user_err (Pp.str "case analysis on a private inductive type is not allowed");
  (* Check all the blocks can be eliminated *)
  List.iter (fun ((kni, ni),dep,s) ->
    (* Check that all the blocks can be eliminated to s *)
    let () = if not @@ Inductiveops.is_allowed_elimination sigma ((mib,mib.mind_packets.(ni)),u) s then
        raise (Pretype_errors.error_not_allowed_elimination env sigma rec_hyp s ((kn, ni), u)) in
    (* Check if dep elim is allowed: rec (co)ind records with prim proj can not be eliminated dependently *)
    if dep && not (Inductiveops.has_dependent_elim sigma (mib, mib.mind_packets.(ni)) u) then
      raise (Pretype_errors.error_not_allowed_dependent_elimination env sigma rec_hyp (kni, ni))
  ) lrecspec

  (** Check all the blocks are mutual, and not given twice *)
let check_valid_mutual env sigma (kn, n) mib u lrecspec =
  let _ : int list =
    List.fold_left (fun ln ((kni, ni),dep,s) ->
        (* Check all the blocks are mutual  *)
        let () = if not (QMutInd.equal env kn kni) then
            raise (RecursionSchemeError (env, NotMutualInScheme ((kn, n), (kni, ni)))) in
        (* Check none is given twice *)
        if Int.List.mem ni ln then
          raise (RecursionSchemeError (env, DuplicateInductiveBlock (kn, ni)))
        else ni::ln)
      [n] lrecspec
  in
  ()

let build_mutual_induction_scheme_gen rec_hyp env sigma lrecspec u =
  match lrecspec with
  | (mind,dep,s)::tail ->
      let mib, mip = lookup_mind_specif env mind in
      (* Check the blocks are all mutual, different, and can be eliminated dependently *)
      let () = check_valid_mutual env sigma mind mib u tail in
      let () = check_valid_elimination env sigma mind mib u lrecspec rec_hyp in
      (* Compute values for gen_elim *)
      let listdepkind = (snd mind, mip, dep, s) ::
        List.map (fun ((_,ni), dep, s) -> (ni, mib.mind_packets.(ni), dep, s)) tail in
      (* Get parameters, and generalized them for UnivPoly + TemplatePoly *)
      let (sigma, uparams, nuparams) = get_params_sep sigma mib u in
      (* Compute eliminators' types and terms *)
      let f =
        let* recs_ty = list_mapi
          (fun i _ -> gen_elim_type Termops.Internal.print_constr_env rec_hyp (fst mind) u mib uparams nuparams listdepkind i)
          (List.init (List.length listdepkind) (fun _ -> 2))
        in
        let* recs_tm = list_mapi
          (fun i _ -> gen_elim_term Termops.Internal.print_constr_env rec_hyp (fst mind) u mib uparams nuparams listdepkind i)
          (List.init (List.length listdepkind) (fun _ -> 2))
        in
        return @@ (recs_ty, recs_tm)
      in run env sigma f
  | _ -> anomaly (Pp.str "build_mutual_induction_scheme expects a non empty list of inductive types.")

let build_mutual_induction_scheme env sigma ?(force_mutual=false) lrecspec u =
  let (sigma, (_, recs_tm)) = build_mutual_induction_scheme_gen true env sigma lrecspec u in
  sigma, recs_tm

let build_induction_scheme env sigma (ind, u) dep kind =
  let (sigma, (_, recs_tm)) = build_mutual_induction_scheme_gen true env sigma [(ind, dep, kind)] u in
  (sigma, List.hd recs_tm)

let build_case_analysis_scheme env sigma (ind, u) dep kind =
  let (sigma, (recs_ty, recs_tm)) = build_mutual_induction_scheme_gen false env sigma [(ind, dep, kind)] u in
  (sigma, List.hd recs_tm, List.hd recs_ty)
