(* Note: we can not use the Set module here because we _need_ physical *)
(* equality and there exists no comparison function compatible with    *)
(* physical equality.                                                  *)
module S =
 struct
  let empty = []
  let mem = List.memq
  let add x l = x::l
 end
;;

let extract_open_proof sigma pf =
 let module PT = Proof_type in
 let module L = Logic in
  let sigma = ref sigma in
  let proof_tree_to_constr = Hashtbl.create 503 in
  let unshared_constrs = ref S.empty in
  let rec proof_extractor vl node =
   let constr =
    match node with
       {PT.ref=Some(PT.Prim _,_)} as pf ->
        L.prim_extractor proof_extractor vl pf
	  
     | {PT.ref=Some(PT.Tactic (_,hidden_proof),spfl)} ->
	 let sgl,v = Refiner.frontier hidden_proof in
	 let flat_proof = v spfl in
	 proof_extractor vl flat_proof
	  
     | {PT.ref=Some(PT.Change_evars,[pf])} -> (proof_extractor vl) pf
	  
     | {PT.ref=None;PT.goal=goal} ->
	 let visible_rels =
           Util.map_succeed
             (fun id ->
                (* Section variables are in the [id] list but are not *)
                (* lambda abstracted in the term [vl]                 *)
                try let n = Util.list_index id vl in (n,id)
	        with Not_found -> failwith "caught")
(*CSC: the above function must be modified such that when it is found  *)
(*CSC: it becomes a Rel; otherwise a Var. Then it can be already used  *)
(*CSC: as the evar_instance. Ordering the instance becomes useless (it *)
(*CSC: will already be ordered.                                        *)
             (Termops.ids_of_named_context goal.Evd.evar_hyps) in
	 let sorted_rels =
	   Sort.list (fun (n1,_) (n2,_) -> n1 > n2 ) visible_rels in
	 let context =
          List.map
            (fun (_,id) -> Sign.lookup_named id goal.Evd.evar_hyps)
            sorted_rels
         in
(*CSC: the section variables in the right order must be added too *)
         let evar_instance = List.map (fun (n,_) -> Term.mkRel n) sorted_rels in
         let env = Global.env_of_context context in
         let sigma',evar =
          Evarutil.new_isevar_sign env !sigma goal.Evd.evar_concl evar_instance
         in
         sigma := sigma' ;
         evar
	  
     | _ -> Util.anomaly "Bug : a case has been forgotten in proof_extractor"
   in
    let unsharedconstr =
     Term.unshare
      ~already_unshared:(function e -> S.mem e !unshared_constrs) constr
    in
     Hashtbl.add proof_tree_to_constr node unsharedconstr ;
     unshared_constrs := S.add unsharedconstr !unshared_constrs ;
     unsharedconstr
  in
  let pfterm = proof_extractor [] pf in
  (pfterm, !sigma, proof_tree_to_constr)
;;

let extract_open_pftreestate pts =
  extract_open_proof (Refiner.evc_of_pftreestate pts)
   (Refiner.proof_of_pftreestate pts)
;;
