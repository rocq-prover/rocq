(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Util
open Term
open Environ
open Declarations
open Cime
open Reduction
open Typeops
open Symbol
open Entries
open Names
open Ordering
open Precedence
open Positivity

(* check monotone arguments *)
let check_mons arity mons antimons =
  let f i =
    if List.mem i mons then (
      if List.mem i antimons then
	error (string_of_int i ^
	       " is declared both monotone and anti-monotone.")
      else Pos
    ) else (
      if List.mem i antimons then Neg
      else Nul
    )
  in Array.init arity f

(* say if a type is compatible with commutativity alone *)
let check_C t =
  match kind_of_term t with
    | Prod (Anonymous,u,v) ->
	(match kind_of_term v with
	   | Prod (Anonymous,u',v) -> eq_constr u u'
	   | _ -> false)
    | _ -> false

(* say if a type is compatible with commutativity and associativity *)
let check_AC t =
  match kind_of_term t with
    | Prod (Anonymous,u,v) ->
	(match kind_of_term v with
	   | Prod (Anonymous,u',u'') -> eq_constr u u' & eq_constr u u''
	   | _ -> false)
    | _ -> false

(* say if a type is compatible with an equational theory *)
let check_eqth = function
  | C -> check_C
  | AC -> check_AC
  | _ -> fun _ -> true

(* say if a constr is headed by a symbol *)
let is_symbol_headed env c =
  match kind_of_term (collapse c) with
    | App (f,_) ->
        (match kind_of_term f with
	   | Const kn -> is_symbol (lookup_constant kn env)
	   | _ -> false)
    | Const kn -> is_symbol (lookup_constant kn env)
    | _ -> false

(* get head symbol of a symbol headed term *)
let head_symbol c =
  match kind_of_term (collapse c) with
    | App (f,_) ->
	(match kind_of_term f with
	   | Const kn -> kn
	   | _ -> invalid_arg "head_symbol")
    | Const kn -> kn
    | _ -> invalid_arg "head_symbol"

(* get head symbol and its arguments *)
let head_symbol_and_args c =
  match kind_of_term (collapse c) with
    | App (f,va) ->
	(match kind_of_term f with
	   | Const kn -> (kn,va)
	   | _ -> invalid_arg "head_symbol")
    | Const kn -> (kn,[||])
    | _ -> invalid_arg "head_symbol"

(* say if a constr is algebraic *)
let is_algebraic env =
  let rec is_alg c =
    match kind_of_term (collapse c) with
      | App (f,va) ->
	  (match kind_of_term f with
	     | Const kn -> is_symbol (lookup_constant kn env)
		 & array_for_all is_alg va
             | Construct _ -> array_for_all is_alg va
	     | _ -> false)
      | Construct _ | Rel _ -> true
      | Const kn -> is_symbol (lookup_constant kn env)
      | _ -> false
  in is_alg

(* compute accessibility of arguments *)
let check_access env ar t =
  let l,u = decompose_prod_n ar t in
    match kind_of_term (get_head u) with
      | Ind (kn,_) ->
	  let f (_,v) = occur_mind env kn Pos v in  
	    array_init_by_list_map ar false f l
      | Const kn ->
	  let f (_,v) = occur_const env kn Pos v in  
	    array_init_by_list_map ar false f l
      | _ -> Array.make ar false

(* check that a symbol declaration is correct *)
let check_symbol env t se =
  let ar = se.symb_entry_arity and eq = se.symb_entry_eqth
  and st = se.symb_entry_status and mons = se.symb_entry_mons
  and antimons = se.symb_entry_mons and prec_defs = se.symb_entry_prec_defs in
    if nb_prod t < ar then error "Type not compatible with arity.";
    if not (check_eqth eq t) then
      error "Type not compatible with equational theory";
    let deltas = check_mons ar mons antimons
    and accs = check_access env ar t in
    { symb_arity = ar; symb_eqth = eq;
      symb_status = st; symb_mons = deltas;
      symb_termin = General_Schema; symb_acc = accs;
      symb_prec_defs = prec_defs }

(* say if a constr is an admissible RHS *)
let is_wf_rhs env =
  let rec is_wf c =
    match kind_of_term c with
      | App (f,va) -> is_wf f & array_for_all is_wf va
      | Construct _ | Ind _ | Const _ | Rel _ -> true
      | Prod (_,t,b) | Lambda (_,t,b) -> is_wf t & is_wf b
      | _ -> false
  in is_wf

(* say if an algebraic constr is linear *)
let is_linear =
  let vars = ref [] in
  let rec is_lin c =
    match kind_of_term c with
      | Rel i -> if List.mem i !vars then false else (vars := i::!vars; true)
      | App (f,va) -> is_lin f; array_for_all is_lin va
      | _ -> true
  in fun c -> vars := []; is_lin c

(* say if an algebraic rule if non-duplicating *)
let is_non_dupl =
  let vars = ref (Array.make 10 0) in
  let init() = Array.fill !vars 0 (Array.length !vars) 0
  and update func i =
    let n = Array.length !vars in
      if i >= n then vars := Array.append !vars (Array.make (i-n+10) 0);
      !vars.(i) <- func !vars.(i)
  in
  let occs func =
    let rec occs_rec c =
      match kind_of_term c with
	| Rel i -> update func i
	| App (f,va) -> occs_rec f; Array.iter occs_rec va
	| _ -> ()
    in occs_rec
  in fun (l,r) -> init(); occs succ l; occs pred r;
    array_for_all (fun v -> v >= 0) !vars

(* check subject reduction *)
let is_welltyped env envl envr (l,r) =
  let kn,args = head_symbol_and_args l in
  let cb = lookup_constant kn env in
  let t = hnf_prod_applist env cb.const_type (Array.to_list args) in
  let tl = j_type (typing envl l) and tr = j_type (typing envr r) in
    try let _ = conv envl tl t and _ = conv envr tr t in true
    with NotConvertible -> false

(* sets of integers *)
module IntOrd = struct
  type t = int
  let compare = Pervasives.compare
end
module IntSet = Set.Make(IntOrd)

(* compute the variables accessible in an array of algebraic terms *)
let acc_vars env =
  let rec accs c =
    match kind_of_term (collapse_appl c) with
      | App (f,va) ->
	  (match kind_of_term f with
	     | Const kn ->
		 (match (lookup_constant kn env).const_symb with
		    | Some si ->
			let f i s c =
			  if si.symb_acc.(i) then IntSet.union s (accs c)
			  else s
			and vb =
			  if Array.length va <= si.symb_arity then va
			  else Array.sub va 0 si.symb_arity
			in array_fold_left_i f IntSet.empty vb
		    | _ -> IntSet.empty)
	     | Construct _ -> Array.fold_left add_accs IntSet.empty va
	     | _ -> IntSet.empty)
      | Rel i -> IntSet.singleton i
      | _ -> IntSet.empty
  and add_accs s c = IntSet.union s (accs c)
  in Array.fold_left add_accs IntSet.empty

(* say if symbols in [c] are smaller or equivalent to [kn]
          symbols equivalent to [kn] are applied to arguments smaller than [vl]
          variables in [c] are accessible in [vl] *)
let are_rec_calls_smaller env prec kn status vl =
  let accs = acc_vars env vl in
  let rec are_rc_smaller c =
    match kind_of_term c with
      | App (f,va) ->
	  begin
	    match kind_of_term f with
	      | Const kn' ->
		  begin
		    match compare prec kn' kn with
		      | Smaller -> array_for_all are_rc_smaller va
		      | Equivalent -> is_struct_smaller_vec status va vl
			  & array_for_all are_rc_smaller va
		      | _ -> false
		  end
	      | _ -> are_rc_smaller f & array_for_all are_rc_smaller va
	  end
      | Const kn' -> compare prec kn' kn = Smaller
      | Construct _ | Ind _ -> true
      | Rel i -> IntSet.mem i accs
      | Lambda (_,t,b) | Prod (_,t,b) -> are_rc_smaller t & are_rc_smaller b
      | _ -> false
  in are_rc_smaller

(* say if a rule satisfies the General Schema *)
let satisfies_GS env (l,r) =
  let kn,vl = head_symbol_and_args l in
  let cb = lookup_constant kn env in
  are_rec_calls_smaller env (prec env) kn (status cb) vl r

(* check that the addition of some rules is correct *)
let check_rules env re =

  (* check context and substitution *)
  let ctx = List.map (fun (id,t) -> (id,LocalAssum t)) re.rules_entry_ctx
  and subs = List.map (fun (id,t) -> (id,LocalDef t)) re.rules_entry_subs in
  let envr,ctx',_ = infer_local_decls env ctx in
  let envl,subs',_ = infer_local_decls envr subs in
  let rules = re.rules_entry_list in

  (* check rule syntax *)
  let is_rule_ok (l,r) = is_algebraic env l
			& is_symbol_headed env l
			& is_wf_rhs env r
  in
    if not (List.for_all is_rule_ok rules)
    then error "There is an ill-formed rule.";

  (* check subject reduction *)
  if not (List.for_all (is_welltyped env envl envr) rules)
  then error "There is a not type-preserving rule.";

  (* check local confluence *)
  if not (is_locally_confluent (cime env) rules)
  then error "Non-confluent rules.";

  (* check left-linearity *)
  let is_left_linear (l,_) = is_linear l in
    if not (List.for_all is_left_linear rules)
    then error "There is a not left-linear rule.";

  (* check termination *)
  if not (List.for_all (satisfies_GS env) rules)
  then error "There is a rule not satisfying the termination criterion.";

  (* end check_rules *)
  print_endline "Rules accepted.";
  { rules_ctx = ctx'; rules_subs = subs'; rules_list = rules }
