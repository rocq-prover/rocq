(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open CErrors
open Util
open Constr
open Environ
open Evd
open Printer

module NamedDecl = Context.Named.Declaration

(* This is set on by proofgeneral proof-tree mode. But may be used for
   other purposes *)
let print_goal_tag_opt_name = ["Printing";"Goal";"Tags"]
let { Goptions.get = should_tag } =
  Goptions.declare_bool_option_and_ref
    ~key:print_goal_tag_opt_name
    ~value:false
    ()

let { Goptions.get = should_unfoc } =
  Goptions.declare_bool_option_and_ref
    ~key:["Printing";"Unfocused"]
    ~value:false
    ()

let { Goptions.get = should_gname } =
  Goptions.declare_bool_option_and_ref
    ~key:["Printing";"Goal";"Names"]
    ~value:false
    ()

let print_goal_name sigma ev =
  should_gname () || Evd.evar_has_unambiguous_name ev sigma

let current_combined = PrintingFlags.current

(* display goal parts (Proof mode) *)

let goal_repr sigma g =
  let EvarInfo evi = Evd.find sigma g in
  let env = Evd.evar_filtered_env (Global.env ()) evi in
  let concl = match Evd.evar_body evi with
  | Evd.Evar_empty -> Evd.evar_concl evi
  | Evd.Evar_defined b -> Retyping.get_type_of env sigma b
  in
  env, concl

(* display complete goal
 og_s has goal+sigma on the previous proof step for diffs
 g_s has goal+sigma on the current proof step
 *)
let pr_goal ?(flags=current_combined()) ?(ogoal=None) sigma g =
  let goal = match ogoal with
  | Some og_s ->
    let g = Proof_diffs.make_goal (Global.env ()) sigma g in
    let (hyps_pp_list, concl_pp) = Proof_diffs.diff_goal ?og_s ~flags g in
    let hyp_list_to_pp hyps =
      match hyps with
      | h :: tl -> List.fold_left (fun x y -> x ++ cut () ++ y) h tl
      | [] -> mt ()
    in
    v 0 (
      (hyp_list_to_pp hyps_pp_list) ++ cut () ++
      str "============================" ++ cut () ++
      concl_pp)
  | None ->
    let env, concl = goal_repr sigma g in
      pr_context_of ~flags env sigma ++ cut () ++
        str "============================" ++ cut ()  ++
        hov 0 (pr_letype_env ~goal_concl_style:true ~flags env sigma concl)
  in
  str "  " ++ v 0 goal

(* display a goal tag *)
let pr_goal_tag g =
  let s = " (ID " ^ Proof.goal_uid g ^ ")" in
  str s

(* display a goal name *)
let pr_goal_name sigma g =
  if print_goal_name sigma g then str " " ++ Pp.surround (pr_existential_key (Global.env ()) sigma g)
  else mt ()

let pr_goal_header nme sigma g =
  str "goal " ++ nme ++ (if should_tag() then pr_goal_tag g else str"")
  ++ (if print_goal_name sigma g then str " " ++ Pp.surround (pr_existential_key (Global.env ()) sigma g) else mt ())

(* display the conclusion of a goal *)
let pr_concl ?(flags=current_combined()) n ?(ogoal=None) sigma g =
  let env, concl = goal_repr sigma g in
  let pc = match ogoal with
  | Some og_s ->
      Proof_diffs.diff_concl ?og_s ~flags (Proof_diffs.make_goal env sigma g)
  | None ->
      pr_letype_env ~goal_concl_style:true ~flags env sigma concl
  in
  let header = pr_goal_header (int n) sigma g in
  header ++ str " is:" ++ cut () ++ str" "  ++ pc

let get_goal_map oldp proof =
  match oldp with
  | _ when not (Proof_diffs.show_diffs ()) -> None
  | Some None -> Some None (* do diffs for first step in proof (ie, no previous proof state) *)
  | Some (Some op) -> (* do diffs *)
    Some (try Some (Proof_diffs.make_goal_map op proof)
    with Pp_diff.Diff_Failure msg ->
      Proof_diffs.notify_proof_diff_failure msg;
      None)
  | None -> None (* don't do diffs *)

let get_ogoal goal_map g =
  let get_ogs map g =
    match map with
    | None -> None
    | Some map -> Proof_diffs.map_goal g map
  in
  Option.map (fun map -> get_ogs map g) goal_map

let pr_selected_subgoal ?(flags=current_combined()) ?(ogoal=None) name sigma g =
  let pg = pr_goal ~flags ~ogoal sigma g in
  let header = pr_goal_header name sigma g in
  v 0 (header ++ str " is:" ++ cut () ++ pg)

let pr_subgoal ~flags oldp proof n sigma =
  let rec prrec p = function
    | [] -> user_err Pp.(str "No such goal.")
    | g::rest ->
        if Int.equal p 1 then
          let goal_map = get_goal_map oldp proof in
          let ogoal = get_ogoal goal_map g in
          pr_selected_subgoal ~flags ~ogoal (int n) sigma g
        else
          prrec (p-1) rest
  in
  prrec n

let pr_internal_existential_key ev = Evar.print ev

let print_evar_constraints ?(flags=current_combined()) gl sigma =
  let pr_env =
    match gl with
    | None -> fun e' -> pr_context_of e' ~flags sigma
    | Some g ->
       let env, _ = goal_repr sigma g in fun e' ->
       begin
         if Context.Named.equal Sorts.relevance_equal Constr.equal (named_context env) (named_context e') then
           if Context.Rel.equal Sorts.relevance_equal Constr.equal (rel_context env) (rel_context e') then mt ()
           else pr_rel_context_of ~flags e' sigma ++ str " |-" ++ spc ()
         else pr_context_of ~flags e' sigma ++ str " |-" ++ spc ()
       end
  in
  let pr_evconstr (pbty,env,t1,t2) =
    let t1 = Evarutil.nf_evar sigma t1
    and t2 = Evarutil.nf_evar sigma t2 in
    let env =
      (* We currently allow evar instances to refer to anonymous de Bruijn
         indices, so we protect the error printing code in this case by giving
         names to every de Bruijn variable in the rel_context of the conversion
         problem. MS: we should rather stop depending on anonymous variables, they
         can be used to indicate independency. Also, this depends on a strategy for
         naming/renaming *)
      Namegen.make_all_name_different env sigma in
    str" " ++
      hov 2 (pr_env env ++ pr_leconstr_env ~flags env sigma t1 ++ spc () ++
             str (match pbty with
                  | Conversion.CONV -> "=="
                  | Conversion.CUMUL -> "<=") ++
             spc () ++ pr_leconstr_env ~flags env sigma t2)
  in
  let pr_candidate ev evi (candidates,acc) =
    if Option.has_some (Evd.evar_candidates evi) then
      (succ candidates, acc ++ pr_evar ~flags sigma (ev,evi) ++ fnl ())
    else (candidates, acc)
  in
  let constraints =
    let _, cstrs = Evd.extract_all_conv_pbs sigma in
    if List.is_empty cstrs then mt ()
    else fnl () ++ str (String.plural (List.length cstrs) "unification constraint")
         ++ str":" ++ fnl () ++ hov 0 (prlist_with_sep fnl pr_evconstr cstrs)
  in
  let candidates, ppcandidates = Evd.fold_undefined pr_candidate sigma (0,mt ()) in
  constraints ++
    if candidates > 0 then
      fnl () ++ str (String.plural candidates "existential") ++
        str" with candidates:" ++ fnl () ++ hov 0 ppcandidates
    else mt ()

let { Goptions.get = should_print_dependent_evars } =
  Goptions.declare_bool_option_and_ref
    ~key:["Printing";"Dependent";"Evars";"Line"]
    ~value:false
    ()

let evar_nodes_of_term c =
  let rec evrec acc c =
    match kind c with
    | Evar (n, l) -> Evar.Set.add n (SList.Skip.fold evrec acc l)
    | _ -> Constr.fold evrec acc c
  in
  evrec Evar.Set.empty (EConstr.Unsafe.to_constr c)

(* spiwack: a few functions to gather evars on which goals depend. *)
let queue_set q is_dependent set =
  Evar.Set.iter (fun a -> Queue.push (is_dependent,a) q) set
let queue_term q is_dependent c =
  queue_set q is_dependent (evar_nodes_of_term c)

let process_dependent_evar q acc evm is_dependent e =
  let EvarInfo evi = Evd.find evm e in
  (* Queues evars appearing in the types of the goal (conclusion, then
     hypotheses), they are all dependent. *)
  let () = match Evd.evar_body evi with
  | Evar_empty ->
    queue_term q true (Evd.evar_concl evi)
  | Evar_defined b ->
    let env = Evd.evar_filtered_env (Global.env ()) evi in
    queue_term q true (Retyping.get_type_of env evm b)
  in
  List.iter begin fun decl ->
    let open NamedDecl in
    queue_term q true (NamedDecl.get_type decl);
    match decl with
    | LocalAssum _ -> ()
    | LocalDef (_,b,_) -> queue_term q true b
  end (EConstr.named_context_of_val (Evd.evar_hyps evi));
  match Evd.evar_body evi with
  | Evar_empty ->
      if is_dependent then Evar.Map.add e None acc else acc
  | Evar_defined b ->
      let subevars = evar_nodes_of_term b in
      (* evars appearing in the definition of an evar [e] are marked
         as dependent when [e] is dependent itself: if [e] is a
         non-dependent goal, then, unless they are reach from another
         path, these evars are just other non-dependent goals. *)
      queue_set q is_dependent subevars;
      if is_dependent then Evar.Map.add e (Some subevars) acc else acc

(** [gather_dependent_evars evm seeds] classifies the evars in [evm]
    as dependent_evars and goals (these may overlap). A goal is an evar
    appearing in the (partial) definition [seeds] (including defined evars). A
    dependent evar is an evar appearing in the type
    (hypotheses and conclusion) of a goal, or in the type or (partial)
    definition of a dependent evar.  The value return is a map
    associating to each dependent evar [None] if it has no (partial)
    definition or [Some s] if [s] is the list of evars appearing in
    its (partial) definition. This completely breaks the EConstr abstraction. *)
let gather_dependent_evars evm l =
  let q = Queue.create () in
  List.iter (queue_term q false) l;
  let acc = ref Evar.Map.empty in
  while not (Queue.is_empty q) do
    let (is_dependent,e) = Queue.pop q in
    (* checks if [e] has already been added to [!acc] *)
    begin if not (Evar.Map.mem e !acc) then
        acc := process_dependent_evar q !acc evm is_dependent e
    end
  done;
  !acc

(* /spiwack *)

let gather_dependent_evars_goal sigma goals =
  let map evk =
    let EvarInfo evi = Evd.find sigma evk in
    EConstr.mkEvar (evk, Evd.evar_identity_subst evi)
  in
  gather_dependent_evars sigma (List.map map goals)

let print_dependent_evars_core gl sigma evars =
  let mt_pp = mt () in
  let evars_pp = Evar.Map.fold (fun e i s ->
      let e' = pr_internal_existential_key e in
      let sep = if s = mt_pp then "" else ", " in
      s ++ str sep ++ e' ++
      (match i with
       | None -> str ":" ++ (Termops.pr_existential_key (Global.env ()) sigma e)
       | Some i ->
         let using = Evar.Set.fold (fun d s ->
             s ++ str " " ++ (pr_internal_existential_key d))
             i mt_pp in
         str " using" ++ using))
      evars mt_pp
  in
  let evars_current_pp = match gl with
    | None -> mt_pp
    | Some gl ->
      let evars_current = gather_dependent_evars_goal sigma [gl] in
      Evar.Map.fold (fun e _ s ->
          s ++ str " " ++ (pr_internal_existential_key e))
        evars_current mt_pp
  in
  cut () ++ cut () ++
  str "(dependent evars: " ++ evars_pp ++
  str "; in current goal:" ++ evars_current_pp ++ str ")"


let print_dependent_evars gl sigma seeds =
  if should_print_dependent_evars () then
    let evars = gather_dependent_evars_goal sigma seeds in
    print_dependent_evars_core gl sigma evars
  else mt ()

let print_dependent_evars_entry gl sigma = function
  | None -> mt ()
  | Some entry ->
    if should_print_dependent_evars () then
      let terms = List.map pi2 (Proofview.initial_goals entry) in
      let evars = gather_dependent_evars sigma terms in
      print_dependent_evars_core gl sigma evars
    else mt ()

(* Print open subgoals. Checks for uninstantiated existential variables *)
(* spiwack: [entry] is for printing dependent evars in emacs mode. *)
(* spiwack: [pr_first] is true when the first goal must be singled out
   and printed in its entirety. *)
(* [os_map] is derived from the previous proof step, used for diffs *)
let pr_subgoals ?(pr_first=true) ?goalmap ?entry
    ~flags sigma ~shelf ~stack ~unfocused ~goals =

  (* Printing functions for the extra informations. *)
  let rec print_stack a = function
    | [] -> Pp.int a
    | b::l -> Pp.int a ++ str"-" ++ print_stack b l
  in
  let print_unfocused_nums l =
    match l with
    | [] -> None
    | a::l -> Some (str"unfocused: " ++ print_stack a l)
  in
  let print_shelf l =
    match l with
    | [] -> None
    | _ -> Some (str"shelved: " ++ Pp.int (List.length l))
  in
  let rec print_comma_separated_list a l =
    match l with
    | [] -> a
    | b::l -> print_comma_separated_list (a++str", "++b) l
  in
  let print_extra_list l =
    match l with
    | [] -> Pp.mt ()
    | a::l -> Pp.spc () ++ str"(" ++ print_comma_separated_list a l ++ str")"
  in
  let extra = Option.List.flatten [ print_unfocused_nums stack ; print_shelf shelf ] in
  let print_extra = print_extra_list extra in
  let focused_if_needed =
    let needed = not (CList.is_empty extra) && pr_first in
    if needed then str" focused "
    else str" " (* non-breakable space *)
  in

  let rec pr_rec n = function
    | [] -> (mt ())
    | g::rest ->
      let ogoal = get_ogoal goalmap g in
      let pc = pr_concl ~flags n ~ogoal sigma g in
        let prest = pr_rec (n+1) rest in
        (cut () ++ pc ++ prest)
  in
  let print_multiple_goals g l =
    if pr_first then
      let ogoal = get_ogoal goalmap g in
      pr_goal ~flags ~ogoal sigma g
      ++ (if l=[] then mt () else cut ())
      ++ pr_rec 2 l
    else
      pr_rec 1 (g::l)
  in
  let pr_evar_info gl =
    let first_goal = if pr_first then gl else None in
    print_evar_constraints ~flags gl sigma ++ print_dependent_evars_entry first_goal sigma entry
  in

  (* Main function *)
  match goals with
  | [] ->
    let exl = Evd.undefined_map sigma in
    if Evar.Map.is_empty exl then
      v 0 (str "No more goals." ++ pr_evar_info None)
    else
      let pei = pr_evars_int ~flags sigma ~shelf ~given_up:[] 1 exl in
      v 0 ((str "No more goals,"
          ++ str " but there are non-instantiated existential variables:"
          ++ cut () ++ (hov 0 pei)
          ++ pr_evar_info None
          ++ cut () ++ str "You can use Unshelve."))
  | g1::rest ->
      let goals = print_multiple_goals g1 rest in
      let ngoals = List.length rest+1 in
      v 0 (
        hov 0 (int ngoals ++ focused_if_needed ++ str(String.plural ngoals "goal")
               ++ print_extra)
        ++ str (if pr_first && (should_gname()) && ngoals > 1 then ", goal 1" else "")
        ++ (if pr_first && should_tag() then pr_goal_tag g1 else str"")
        ++ (if pr_first then pr_goal_name sigma g1 else mt()) ++ cut () ++ goals
        ++ (if unfocused=[] then str ""
           else (cut() ++ cut() ++ str "*** Unfocused goals:" ++ cut()
                 ++ pr_rec (List.length rest + 2) unfocused))
        ++ pr_evar_info (Some g1)
      )

let pr_open_subgoals ?(quiet=false) ?(oldp=None) ?(flags=current_combined()) proof =
  (* spiwack: it shouldn't be the job of the printer to look up stuff
     in the [evar_map], I did stuff that way because it was more
     straightforward, but seriously, [Proof.proof] should return
     [evar_info]-s instead. *)
  let p = proof in
  let Proof.{goals; stack; sigma;entry} = Proof.data p in
  let shelf = Evd.shelf sigma in
  let given_up = Evd.given_up sigma in
  let stack = List.map (fun (l,r) -> List.length l + List.length r) stack in
  begin match goals with
  | [] -> let bgoals = Proof.background_subgoals p in
          begin match bgoals,shelf,given_up with
          | [] , [] , g when Evar.Set.is_empty g -> pr_subgoals ~flags sigma ~entry ~shelf ~stack ~unfocused:[] ~goals
          | [] , [] , _ ->
             Feedback.msg_info (str "No more goals, but there are some goals you gave up:");
             fnl ()
            ++ pr_subgoals ~pr_first:false ~flags sigma ~entry ~shelf:[] ~stack:[] ~unfocused:[] ~goals:(Evar.Set.elements given_up)
            ++ fnl () ++ str "You need to go back and solve them."
          | [] , _ , _ ->
            Feedback.msg_info (str "All the remaining goals are on the shelf.");
            fnl ()
            ++ pr_subgoals ~pr_first:false ~flags sigma ~entry ~shelf:[] ~stack:[] ~unfocused:[] ~goals:shelf
          | _ , _, _ ->
            let () =
              if quiet then ()
              else
              Feedback.msg_info
                (str "This subproof is complete, but there are some unfocused goals." ++
                (let s = Proof_bullet.suggest p in
                 if Pp.ismt s then s else fnl () ++ s) ++
                fnl ())
            in
            pr_subgoals ~pr_first:false ~flags sigma ~entry ~shelf ~stack:[] ~unfocused:[] ~goals:bgoals
          end
  | _ ->
     let bgoals = Proof.background_subgoals p in
     let bgoals_focused, bgoals_unfocused = List.partition (fun x -> List.mem x goals) bgoals in
     let unfocused_if_needed = if should_unfoc() then bgoals_unfocused else [] in
     let goalmap = get_goal_map oldp proof in
     pr_subgoals ~flags ~pr_first:true ?goalmap sigma ~entry ~shelf ~stack:[]
        ~unfocused:unfocused_if_needed ~goals:bgoals_focused
  end

let pr_nth_open_subgoal ?(flags=current_combined()) ?(oldp=None) ~proof n =
  let Proof.{goals;sigma} = Proof.data proof in
  pr_subgoal ~flags oldp proof n sigma goals

let pr_goal_by_id ?(flags=current_combined()) ?(oldp=None) ~proof id =
  try
    let { Proof.sigma } = Proof.data proof in
    let g = Evd.evar_key id sigma in
    let goal_map = get_goal_map oldp proof in
    let ogoal = get_ogoal goal_map g in
    pr_selected_subgoal ~flags ~ogoal (Libnames.pr_qualid id) sigma g
  with Not_found -> user_err Pp.(str "No such goal.")

(** print a goal identified by the goal id as it appears in -emacs mode.
    sid should be the Stm state id corresponding to proof.  Used to support
    the Prooftree tool in Proof General. (https://askra.de/software/prooftree/).
*)
let pr_goal_emacs ?(flags=current_combined()) ~proof gid sid =
  match proof with
  | None -> user_err Pp.(str "No proof for that state.")
  | Some proof ->
    let pr sigma gs =
      v 0 ((str "goal ID " ++ (int gid) ++ str " at state " ++ (int sid)) ++ cut ()
          ++ pr_goal ~flags sigma gs)
    in
    try
      let { Proof.sigma } = Proof.data proof in
      let gl = Evar.unsafe_of_int gid in
      v 0 (pr sigma gl ++ print_dependent_evars (Some gl) sigma [ gl ])
    with Not_found -> user_err Pp.(str "No such goal.")
