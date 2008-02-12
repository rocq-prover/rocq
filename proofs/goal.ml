(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Term

(* This module implements the abstract interface to goals *)
(* A general invariant of the module, is that a goal whose associated 
   evar is defined in the current evar_defs, should not be accessed. *)

(* type of the goals *)
type goal = {
  content : Evd.evar;      (* Corresponding evar. Allows to retrieve
			      logical information once put together
			      with an evar_map. *)
  name : string option     (* Optional name of the goal to be displayed *)
}

(* access primitive *)
(* invariant : [e] must exist in [em] *)
let content evars { content = e } = Evd.find evars e
let name { name = n } = n


(* Builds a new goal named [name] with evar [e] *)
let build ?name e =
  { content = e ;
    name = name
  }


(* Returns [true] if the goal has been partially resolved. *)
let is_defined evars { content = e } = Evd.is_defined evars e



(*** Goal tactics ***)



(* return type of the excution of goal tactics *)
(* it contains the new subgoals to produce, and the definitions of
   the evars to instantiate *)
type refinement = { subgoals: goal list ;
                    new_defs: Evd.evar_defs }



(* type of the base elements of the goal API.*)
(* it has an extra evar_info with respect to what would be expected,
   it is supposed to be the evar_info of the goal in the evar_defs.
   The idea is that it is computed by the [run] function as an 
   optimisation, since it will generaly not change during the 
   evaluation. As a matter of fact it should only change as far
   as caching is concerned, which is of no concern for the tactics
   themselves. *)
type 'a expression = Environ.env -> Evd.evar_defs ref -> goal -> Evd.evar_info -> 'a


(* type of the goal tactics*)
type tactic = refinement expression


(* runs a goal tactic on a given goal (knowing the current evar_defs). *)
(* the evar_info corresponding to the goal is computed at once
   as an optimisation (it usually won't change during the evaluation). 
   As a matter of fact it should only change as far as caching is 
   concerned, which is of no concern for the tactics themselves. *)
let run t env defs gl =
  let info = content (Evd.evars_of defs) gl in
  let env = Environ.reset_with_named_context (Evd.evar_hyps info) env in
  let rdefs = ref defs in
  t env rdefs gl info


(* a pessimistic (i.e : there won't be many positive answers) filter
   over evar_maps *)
let evar_map_filter f evm =
  Evd.fold (fun ev evi r -> 
	      if f ev evi then 
		Evd.add r ev evi 
	      else 
		r
	   ) 
           evm 
           Evd.empty

(*arnaud: à déplacer ou du moins à paramètrer. Peut-être à construire
          dans la monade. *)
let open_constr_of_raw check_type rawc env rdefs gl info =
  (* We need to keep trace of what [rdefs] was originally*)
  let init_defs = !rdefs in
  (* if [check_type] is true, then creates a type constraint for the 
     proof-to-be *)
  let tycon = Pretyping.OfType (Option.init check_type (Evd.evar_concl info)) in
  (* call to [understand_tcc_evars] returns a constr with undefined evars
     these evars will be our new goals *)
  let open_constr = Pretyping.Default.understand_tcc_evars rdefs env tycon rawc
  in
  (* [!rdefs] contains the evar_defs outputed by  [understand_...] *)
  let post_defs = !rdefs in
  (* [delta_evars] holds the evars that have been introduced by this
     refinement (but not immediatly solved) *)
  (* arnaud: probablement à speeder up un bit *)
  (* arnaud: il va probablement même falloir renvoyer les existentials.
     Parce que sinon c'est trop laid à trouver ! *)
  let delta_evars = evar_map_filter (fun ev evi ->
                                      evi.Evd.evar_body = Evd.Evar_empty &&
                                      (* arnaud: factoriser la map ?*)
                                      not (Evd.mem (Evd.evars_of init_defs) ev)
				   )
                                   (Evd.evars_of post_defs)
  in
  (* [delta_evars] in the shape of a list of [evar]-s*)
  let delta_list = List.map fst (Evd.to_list delta_evars) in
  Evd.make_open_constr ~global_defs: post_defs
                       ~my_evars: delta_list
                       ~me: open_constr

(* arnaud: à commenter un brin plus *)
let refine step env rdefs gl info =
  (* subgoals to return *)
  (* arnaud: et les noms? *)
  let subgoals = List.map build (Evd.get_my_evars step) in
  (* creates the new [evar_defs] by defining the evar of the current goal
     as being [refine_step]. *)
  let new_defs = Evd.evar_define gl.content (Evd.get_constr step) !rdefs in
  rdefs := new_defs; 
  { subgoals = subgoals ;
    new_defs = new_defs ;
  }


(* arnaud: faut franchement nettoyer tout ça. Ça mérite une réflexion de fond
   mais ya du nettoyage à faire *)

(* arnaud: c'est évidemment faux. Evarutil.clear_hyps_in_evi change toutes
   les evars en les instanciant, ce qui crée des bugs dans les dépendances.
   Dès les phases où ça doit devenir crédible il faudra repenser sérieusement
   la sémantique de ce truc.
   L'idée serait de ne pas instancier les vieilles evars avec de nouveau
   trucs, mais de faire de nouveau trucs instanciés par les vieilles evars.
   Ou bien de demander à l'autre but de suivre l'instanciation du clear.
   Je pense.
   - A la réflexion, si un but fait référence à l'evar ?x et qu'on prétend
   (sémantique de clear) qu'on peut le résoudre sans y, alors on prétend aussi
   que y n'a pas d'importance dans ?x. Cependant, on peut enlever ?x avant si
   il faut. Le défaut de ce procédé c'est qu'on modifie des buts auquels on
   n'a censément pas accès à ce moment de l'exécution de cette tactique.
   Il faut donc un moyen de les faire "avancer", (car sinon il vont 
   disparaître). Peut-être une info dans l'evar_info, il est là pour ça
   après tout.
   *)
(* Implements the clear tactic *)
(* arnaud: wrapper les erreurs autour de [clear_in_evi] dans une tactic
   failure, avec une output stream inspirée de l'ancien clear_in_evi *)
let clear idents _ rdefs gl info =
  let cleared_info = Evarutil.clear_in_evi rdefs info idents in
  let cleared_env = Environ.reset_with_named_context (Evd.evar_hyps cleared_info) 
                                                     Environ.empty_env in
  let cleared_concl = Evd.evar_concl cleared_info in
  let clearing_constr = Evarutil.e_new_evar rdefs cleared_env cleared_concl in
  let cleared_evar = match kind_of_term clearing_constr with
                     | Evar (e,_) -> e
		     | _ -> Util.anomaly "Goal.clear: e_new_evar failure"
  in
  let cleared_goal = build cleared_evar in
  rdefs := Evd.evar_define gl.content clearing_constr !rdefs;
  { subgoals = [cleared_goal] ;
    new_defs = !rdefs
  }


(* arnaud: générer les erreurs en deux temps sans doute ? *)
(* arnaud: qu'est-ce qui doit être failure, et qu'est-ce qui doit juste
   failer de progresser ?*)
(* the four following functions implement the clearbody tactic *)
let apply_to_hyp_and_dependent_on sign id f g =
  try Environ.apply_to_hyp_and_dependent_on sign id f g 
  with Environ.Hyp_not_found -> 
    (*arnaud: if !check then*) Util.error "No such assumption" (*arnaud: error ou pas ?*)
    (*arnaud: ça va avec le !check d'au dessus: else sign*)

let check_typability env sigma c =
  (*arnaud:if !check then*) let _ = Typing.type_of env sigma c in () 

(* arnaud: est-il intéressant de rajouter un no-check flag ? *)
let recheck_typability (what,id) env sigma t =
  try check_typability env sigma t
  with _ ->
    let s = match what with
      | None -> "the conclusion"
      | Some id -> "hypothesis "^(Names.string_of_id id) in
    Util.error (*arnaud: error ou pas ?*)
      ("The correctness of "^s^" relies on the body of "^(Names.string_of_id id))

let remove_hyp_body env sigma id =
  let sign =
    apply_to_hyp_and_dependent_on (Environ.named_context_val env) id
      (fun (_,c,t) _ ->
	match c with
	| None -> Util.error ((Names.string_of_id id)^" is not a local definition") (*arnaud: error ou pas ?*)
	| Some c ->(id,None,t))
      (fun (id',c,t as d) sign ->
	((* arnaud: if !check then*)
	  begin 
	    let env = Environ.reset_with_named_context sign env in
	    match c with
	    | None ->  recheck_typability (Some id',id) env sigma t
	    | Some b ->
		let b' = mkCast (b,DEFAULTcast, t) in
		recheck_typability (Some id',id) env sigma b'
	  end;d))
  in
  Environ.reset_with_named_context sign env 

(* arnaud: on fait autant de passe qu'il y a d'hypothèses, ça permet un 
   message d'erreur plus fin, mais c'est un peu lourdingue...*)
let clear_body env idents rdefs gl =
  let info = content (Evd.evars_of !rdefs) gl in
  let full_env = Environ.reset_with_named_context (Evd.evar_hyps info) env in
  let aux env id = 
     let env' = remove_hyp_body env (Evd.evars_of !rdefs) id in
       (*arnaud: if !check then*) recheck_typability (None,id) env' (Evd.evars_of !rdefs) (Evd.evar_concl info);
       env'
  in
  let new_env = 
    List.fold_left aux full_env idents
  in
  let concl = Evd.evar_concl info in
  let (defs',new_constr) = Evarutil.new_evar !rdefs new_env concl in
  let new_evar = match kind_of_term new_constr with
                     | Evar (e,_) -> e
		     | _ -> Util.anomaly "Goal.clear: e_new_evar failure"
  in
  let new_goal = build new_evar in
  rdefs := Evd.evar_define gl.content new_constr defs';
  { subgoals = [new_goal] ;
    new_defs = !rdefs
  }

(* arnaud Evarutil ou Reductionops ou Pretype_errors .nf_evar? *)




(*** Expressions & Tacticals ***)


(* if then else on expressions *)
let cond b ~thn ~els env rdefs goal info =
  if b env rdefs goal info then
    thn env rdefs goal info
  else 
    els env rdefs goal info

(* monadic bind on expressions *)
let bind e f env rdefs goal info =
  f (e env rdefs goal info) env rdefs goal info

(* monadic return on expressions *)
let return v _ _ _ _ = v

(* changes a list of expressions into an list expression *)
let expr_of_list l env rdefs goal info = 
  List.map (fun x -> x env rdefs goal info) l

(* map combinator which may usefully complete [bind] *)
let map f e env rdefs goal info =
  f (e env rdefs goal info)

(* binary map combinator *)
let map2 f e1 e2 env rdefs goal info =
  f (e1 env rdefs goal info) (e2 env rdefs goal info)


(* [concl] is the conclusion of the current goal *)
let concl _ _ _ info =
  Evd.evar_concl info

(* [hyps] is the [named_context_val] representing the hypotheses
   of the current goal *)
let hyps _ _ _ info =
  Evd.evar_hyps info

(* [env] is the current [Environ.env] containing both the 
   environment in which the proof is ran, and the goal hypotheses *)
let env env _ _ _ = env

(* [defs] is the [Evd.evar_defs] at the current evaluation point *)
let defs _ rdefs _ _ =
  !rdefs
  
(* arnaud: remplacer par un "print goal" I guess suppose. 
(* This function returns a new goal where the evars have been
   instantiated according to an evar_map *)
let instantiate em gl =
  (* note: goals don't have an evar_body *)
  let content = gl.content in
  let instantiate =  Evarutil.nf_evar em in
  { gl with
  
    content = { content with
                (* arnaud: map_named_val est a priori ok: si [t] n'a pas
		   d'evar alors [instantiate t] = [t], sinon [t] n'a
                   pas de forme compilé donc ça reste correct. Commenter
                   dans environ.ml(i) (et pre_env.ml(i)?) si ça fonctionne.*)
		Evd.evar_hyps = Environ.map_named_val instantiate content.Evd.evar_hyps;
		Evd.evar_concl = instantiate content.Evd.evar_concl
	      }
  }
*)
