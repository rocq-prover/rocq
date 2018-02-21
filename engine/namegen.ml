(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Created from contents that was formerly in termops.ml and
   nameops.ml, Nov 2009 *)

(* This file is about generating new or fresh names and dealing with
   alpha-renaming *)

open Util
open Names
open Term
open Environ
open EConstr
open Vars
open Nametab
open Nameops
open Libnames
open Globnames
open Context.Rel.Declaration

module RelDecl = Context.Rel.Declaration

(**********************************************************************)
(* Conventional names *)

let default_prop_string = "H"
let default_prop_ident = Id.of_string default_prop_string

let default_small_string = "H"
let default_small_ident = Id.of_string default_small_string

let default_type_string = "X"
let default_type_ident = Id.of_string default_type_string

let default_non_dependent_string = "H"
let default_non_dependent_ident = Id.of_string default_non_dependent_string

let default_dependent_ident = Id.of_string "x"

let default_generated_non_letter_string = "x"

(**********************************************************************)
(* Globality of identifiers *)

let is_imported_modpath = function
  | MPfile dp ->
    let rec find_prefix = function
      |MPfile dp1 -> not (DirPath.equal dp1 dp)
      |MPdot(mp,_) -> find_prefix mp
      |MPbound(_) -> false
    in find_prefix (Lib.current_mp ())
  | _ -> false

let is_imported_ref = function
  | VarRef _ -> false
  | IndRef (kn,_)
  | ConstructRef ((kn,_),_) ->
      let (mp,_,_) = MutInd.repr3 kn in is_imported_modpath mp
  | ConstRef kn ->
      let (mp,_,_) = Constant.repr3 kn in is_imported_modpath mp

let is_global id =
  try
    let ref = locate (qualid_of_ident id) in
    not (is_imported_ref ref)
  with Not_found ->
    false

let is_constructor id =
  try
    match locate (qualid_of_ident id) with
      | ConstructRef _ -> true
      | _ -> false
  with Not_found ->
    false

let is_section_variable id =
  try let _ = Global.lookup_named id in true
  with Not_found -> false

(**********************************************************************)
(* Generating "intuitive" names from its type *)

let global_of_constr = function
| Const (c, _) -> ConstRef c
| Ind (i, _) -> IndRef i
| Construct (c, _) -> ConstructRef c
| Var id -> VarRef id
| _ -> assert false

let head_name sigma c = (* Find the head constant of a constr if any *)
  let rec hdrec c =
    match EConstr.kind sigma c with
    | Prod (_,_,c) | Lambda (_,_,c) | LetIn (_,_,_,c)
    | Cast (c,_,_) | App (c,_) -> hdrec c
    | Proj (kn,_,_) -> Some (Label.to_id (Constant.label (Projection.constant kn)))
    | Const _ | Ind _ | Construct _ | Var _ as c ->
	Some (basename_of_global (global_of_constr c))
    | Fix ((_,i),(lna,_,_)) | CoFix (i,(lna,_,_)) ->
	Some (match lna.(i) with Name id -> id | _ -> assert false)
    | Sort _ | Rel _ | Meta _|Evar _|Case (_, _, _, _) -> None
  in
  hdrec c

let lowercase_first_char id = (* First character of a constr *)
  let s = Id.to_string id in
  match Unicode.split_at_first_letter s with
  | None ->
    (* General case: nat -> n *)
    Unicode.lowercase_first_char s
  | Some (s,s') ->
      if String.length s' = 0 then
      (* No letter, e.g. __, or __'_, etc. *)
        default_generated_non_letter_string
      else
        s ^ Unicode.lowercase_first_char s'

let sort_hdchar = function
  | Prop(_) -> "P"
  | Type(_) -> "T"

let hdchar env sigma c =
  let rec hdrec k c =
    match EConstr.kind sigma c with
    | Prod (_,_,c) | Lambda (_,_,c) | LetIn (_,_,_,c) -> hdrec (k+1) c
    | Cast (c,_,_) | App (c,_) -> hdrec k c
    | Proj (kn,_,_) -> lowercase_first_char (Label.to_id (Constant.label (Projection.constant kn)))
    | Const (kn,_) -> lowercase_first_char (Label.to_id (Constant.label kn))
    | Ind (x,_) -> (try lowercase_first_char (basename_of_global (IndRef x)) with Not_found when !Flags.in_debugger -> "zz")
    | Construct (x,_) -> (try lowercase_first_char (basename_of_global (ConstructRef x)) with Not_found when !Flags.in_debugger -> "zz")
    | Var id  -> lowercase_first_char id
    | Sort s -> sort_hdchar (ESorts.kind sigma s)
    | Rel n ->
	(if n<=k then "p" (* the initial term is flexible product/function *)
	 else
	   try match lookup_rel (n-k) env with
	     | LocalAssum (Name id,_)   | LocalDef (Name id,_,_) -> lowercase_first_char id
	     | LocalAssum (Anonymous,t) | LocalDef (Anonymous,_,t) -> hdrec 0 (lift (n-k) t)
	   with Not_found -> "y")
    | Fix ((_,i),(lna,_,_)) | CoFix (i,(lna,_,_)) ->
	let id = match lna.(i) with Name id -> id | _ -> assert false in
	lowercase_first_char id
    | Evar _ (* We could do better... *)
    | Meta _ | Case (_, _, _, _) -> "y"
  in
  hdrec 0 c

let id_of_name_using_hdchar env sigma a = function
  | Anonymous -> Id.of_string (hdchar env sigma a)
  | Name id   -> id

let named_hd env sigma a = function
  | Anonymous -> Name (Id.of_string (hdchar env sigma a))
  | x         -> x

let mkProd_name   env sigma (n,a,b) = mkProd (named_hd env sigma a n, a, b)
let mkLambda_name env sigma (n,a,b) = mkLambda (named_hd env sigma a n, a, b)

let lambda_name = mkLambda_name
let prod_name = mkProd_name

let prod_create   env sigma (a,b) = mkProd (named_hd env sigma a Anonymous, a, b)
let lambda_create env sigma (a,b) =  mkLambda (named_hd env sigma a Anonymous, a, b)

let name_assumption env sigma = function
    | LocalAssum (na,t) -> LocalAssum (named_hd env sigma t na, t)
    | LocalDef (na,c,t) -> LocalDef (named_hd env sigma c na, c, t)

let name_context env sigma hyps =
  snd
    (List.fold_left
       (fun (env,hyps) d ->
	  let d' = name_assumption env sigma d in (push_rel d' env, d' :: hyps))
       (env,[]) (List.rev hyps))

let mkProd_or_LetIn_name env sigma b d = mkProd_or_LetIn (name_assumption env sigma d) b
let mkLambda_or_LetIn_name env sigma b d = mkLambda_or_LetIn (name_assumption env sigma d) b

let it_mkProd_or_LetIn_name env sigma b hyps =
  it_mkProd_or_LetIn b (name_context env sigma hyps)
let it_mkLambda_or_LetIn_name env sigma b hyps =
  it_mkLambda_or_LetIn b (name_context env sigma hyps)

(**********************************************************************)
(* Fresh names *)

(* Looks for next "good" name by lifting subscript *)

let next_ident_away_from id bad =
  let rec name_rec id = if bad id then name_rec (increment_subscript id) else id in
  name_rec id

(* Restart subscript from x0 if name starts with xN, or x00 if name
   starts with x0N, etc *)

let restart_subscript id =
  if not (has_subscript id) then id else
    (* It would probably be better with something in the spirit of
     *** make_ident id (Some 0) *** but compatibility would be lost... *)
    forget_subscript id

let visible_ids sigma (nenv, c) =
  let accu = ref (Refset_env.empty, Int.Set.empty, Id.Set.empty) in
  let rec visible_ids n c = match EConstr.kind sigma c with
  | Const _ | Ind _ | Construct _ | Var _ as c ->
    let (gseen, vseen, ids) = !accu in
    let g = global_of_constr c in
    if not (Refset_env.mem g gseen) then
      begin
      try
      let gseen = Refset_env.add g gseen in
      let short = shortest_qualid_of_global Id.Set.empty g in
      let dir, id = repr_qualid short in
      let ids = if DirPath.is_empty dir then Id.Set.add id ids else ids in
      accu := (gseen, vseen, ids)
      with Not_found when !Flags.in_debugger || !Flags.in_toplevel -> ()
      end
  | Rel p ->
    let (gseen, vseen, ids) = !accu in
    if p > n && not (Int.Set.mem p vseen) then
      let vseen = Int.Set.add p vseen in
      let name =
        try Some (List.nth nenv (p - n - 1))
        with Invalid_argument _ | Failure _ ->
          (* Unbound index: may happen in debug and actually also
             while computing temporary implicit arguments of an
             inductive type *)
          None
      in
      let ids = match name with
      | Some (Name id) -> Id.Set.add id ids
      | _ -> ids
      in
      accu := (gseen, vseen, ids)
  | _ -> EConstr.iter_with_binders sigma succ visible_ids n c
  in
  let () = visible_ids 1 c in
  let (_, _, ids) = !accu in
  ids

(* Now, there are different renaming strategies... *)

(* 1- Looks for a fresh name for printing in cases pattern *)

let next_name_away_in_cases_pattern sigma env_t na avoid =
  let id = match na with Name id -> id | Anonymous -> default_dependent_ident in
  let visible = visible_ids sigma env_t in
  let bad id = Id.Set.mem id avoid || is_constructor id
                                    || Id.Set.mem id visible in
  next_ident_away_from id bad

(* 2- Looks for a fresh name for introduction in goal *)

(* The legacy strategy for renaming introduction variables is not very uniform:
   - if the name to use is fresh in the context but used as a global
     name, then a fresh name is taken by finding a free subscript
     starting from the current subscript;
   - but if the name to use is not fresh in the current context, the fresh
     name is taken by finding a free subscript starting from 0 *)

let next_ident_away_in_goal id avoid =
  let id = if Id.Set.mem id avoid then restart_subscript id else id in
  let bad id = Id.Set.mem id avoid || (is_global id && not (is_section_variable id)) in
  next_ident_away_from id bad

let next_name_away_in_goal na avoid =
  let id = match na with
    | Name id -> id
    | Anonymous -> default_non_dependent_ident in
  next_ident_away_in_goal id avoid

(* 3- Looks for next fresh name outside a list that is moreover valid
   as a global identifier; the legacy algorithm is that if the name is
   already used in the list, one looks for a name of same base with
   lower available subscript; if the name is not in the list but is
   used globally, one looks for a name of same base with lower subscript
   beyond the current subscript *)

let next_global_ident_away id avoid =
  let id = if Id.Set.mem id avoid then restart_subscript id else id in
  let bad id = Id.Set.mem id avoid || is_global id in
  next_ident_away_from id bad

(* 4- Looks for next fresh name outside a list; if name already used,
   looks for same name with lower available subscript *)

let next_ident_away id avoid =
  if Id.Set.mem id avoid then
    next_ident_away_from (restart_subscript id) (fun id -> Id.Set.mem id avoid)
  else id

let next_name_away_with_default default na avoid =
  let id = match na with Name id -> id | Anonymous -> Id.of_string default in
  next_ident_away id avoid

let reserved_type_name = ref (fun t -> Anonymous)
let set_reserved_typed_name f = reserved_type_name := f

let next_name_away_with_default_using_types default na avoid t =
  let id = match na with
    | Name id -> id
    | Anonymous -> match !reserved_type_name t with
	| Name id -> id
	| Anonymous -> Id.of_string default in
  next_ident_away id avoid

let next_name_away = next_name_away_with_default default_non_dependent_string

let make_all_name_different env sigma =
  (** FIXME: this is inefficient, but only used in printing *)
  let avoid = ref (ids_of_named_context_val (named_context_val env)) in
  let sign = named_context_val env in
  let rels = rel_context env in
  let env0 = reset_with_named_context sign env in
  Context.Rel.fold_outside
    (fun decl newenv ->
       let na = named_hd newenv sigma (RelDecl.get_type decl) (RelDecl.get_name decl) in
       let id = next_name_away na !avoid in
       avoid := Id.Set.add id !avoid;
       push_rel (RelDecl.set_name (Name id) decl) newenv)
    rels ~init:env0

(* 5- Looks for next fresh name outside a list; avoids also to use names that
   would clash with short name of global references; if name is already used,
   looks for name of same base with lower available subscript beyond current
   subscript *)

let next_ident_away_for_default_printing sigma env_t id avoid =
  let visible = visible_ids sigma env_t in
  let bad id = Id.Set.mem id avoid || Id.Set.mem id visible in
  next_ident_away_from id bad

let next_name_away_for_default_printing sigma env_t na avoid =
  let id = match na with
  | Name id   -> id
  | Anonymous ->
      (* In principle, an anonymous name is not dependent and will not be *)
      (* taken into account by the function compute_displayed_name_in; *)
      (* just in case, invent a valid name *)
      default_non_dependent_ident in
  next_ident_away_for_default_printing sigma env_t id avoid

(**********************************************************************)
(* Displaying terms avoiding bound variables clashes *)

(* Renaming strategy introduced in December 1998:

   - Rule number 1: all names, even if unbound and not displayed, contribute
     to the list of names to avoid
   - Rule number 2: only the dependency status is used for deciding if
     a name is displayed or not

   Example:
   bool_ind: "forall (P:bool->Prop)(f:(P true))(f:(P false))(b:bool), P b" is
   displayed "forall P:bool->Prop, P true -> P false -> forall b:bool, P b"
   but f and f0 contribute to the list of variables to avoid (knowing
   that f and f0 are how the f's would be named if introduced, assuming
   no other f and f0 are already used).
*)

type renaming_flags =
  | RenamingForCasesPattern of (Name.t list * constr)
  | RenamingForGoal
  | RenamingElsewhereFor of (Name.t list * constr)

let next_name_for_display sigma flags =
  match flags with
  | RenamingForCasesPattern env_t -> next_name_away_in_cases_pattern sigma env_t
  | RenamingForGoal -> next_name_away_in_goal
  | RenamingElsewhereFor env_t -> next_name_away_for_default_printing sigma env_t

(* Remark: Anonymous var may be dependent in Evar's contexts *)
let compute_displayed_name_in_gen_poly noccurn_fun sigma flags avoid na c =
  match na with
  | Anonymous when noccurn_fun sigma 1 c ->
    (Anonymous,avoid)
  | _ ->
    let fresh_id = next_name_for_display sigma flags na avoid in
    let idopt = if noccurn_fun sigma 1 c then Anonymous else Name fresh_id in
    (idopt, Id.Set.add fresh_id avoid)

let compute_displayed_name_in = compute_displayed_name_in_gen_poly noccurn

let compute_displayed_name_in_gen f sigma =
  (* only flag which does not need a constr, maybe to be refined *)
  let flag = RenamingForGoal in
  compute_displayed_name_in_gen_poly f sigma flag

let compute_and_force_displayed_name_in sigma flags avoid na c =
  match na with
  | Anonymous when noccurn sigma 1 c ->
    (Anonymous,avoid)
  | _ ->
    let fresh_id = next_name_for_display sigma flags na avoid in
    (Name fresh_id, Id.Set.add fresh_id avoid)

let compute_displayed_let_name_in sigma flags avoid na c =
  let fresh_id = next_name_for_display sigma flags na avoid in
  (Name fresh_id, Id.Set.add fresh_id avoid)

let rename_bound_vars_as_displayed sigma avoid env c =
  let rec rename avoid env c =
    match EConstr.kind sigma c with
    | Prod (na,c1,c2)  ->
	let na',avoid' =
          compute_displayed_name_in sigma
            (RenamingElsewhereFor (env,c2)) avoid na c2 in
	mkProd (na', c1, rename avoid' (na' :: env) c2)
    | LetIn (na,c1,t,c2) ->
	let na',avoid' =
          compute_displayed_let_name_in sigma
            (RenamingElsewhereFor (env,c2)) avoid na c2 in
	mkLetIn (na',c1,t, rename avoid' (na' :: env) c2)
    | Cast (c,k,t) -> mkCast (rename avoid env c, k,t)
    | _ -> c
  in
  rename avoid env c

(**********************************************************************)
(* "H"-based naming strategy introduced June 2014 for hypotheses in
   Prop produced by case/elim/destruct/induction, in place of the
   strategy that was using the first letter of the type, leading to
   inelegant "n:~A", "e:t=u", etc. when eliminating sumbool or similar
   types *)

let h_based_elimination_names = ref false

let use_h_based_elimination_names () = !h_based_elimination_names

open Goptions

let _ = declare_bool_option
	  { optdepr  = true; (* remove in 8.8 *)
	    optname  = "use of \"H\"-based proposition names in elimination tactics";
	    optkey   = ["Standard";"Proposition";"Elimination";"Names"];
	    optread  = (fun () -> !h_based_elimination_names);
	    optwrite = (:=) h_based_elimination_names }
