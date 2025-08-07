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
open Util
open Names
open Termops
open Environ
open EConstr
open Vars
open Namegen
open Evd
open Tacred
open Logic
open Tacticals
open Tactypes
open Proofview.Notations
open TacticExceptions
open ContextTactics
open ConvTactics
open HypNaming

module RelDecl = Context.Rel.Declaration
module NamedDecl = Context.Named.Declaration

(*******************************************)
(*         Introduction tactics            *)
(*******************************************)

(** This tactic creates a partial proof realizing the introduction rule, but
    does not check anything. *)
let unsafe_intro env decl ~relevance b =
  Refine.refine_with_principal ~typecheck:false begin fun sigma ->
    let ctx = named_context_val env in
    let nctx = push_named_context_val decl ctx in
    let inst = EConstr.identity_subst_val (named_context_val env) in
    let ninst = SList.cons (mkRel 1) inst in
    let nb = subst1 (mkVar (NamedDecl.get_id decl)) b in
    let (sigma, ev) = new_pure_evar nctx sigma ~relevance nb in
    (sigma, mkLambda_or_LetIn (NamedDecl.to_rel_decl decl) (mkEvar (ev, ninst)),
     Some ev)
  end

let introduction id =
  Proofview.Goal.enter begin fun gl ->
    let concl = Proofview.Goal.concl gl in
    let relevance = Proofview.Goal.relevance gl in
    let sigma = Tacmach.project gl in
    let hyps = named_context_val (Proofview.Goal.env gl) in
    let env = Proofview.Goal.env gl in
    let () = if mem_named_context_val id hyps then
      Loc.raise (IntroAlreadyDeclared id)
    in
    let open Context.Named.Declaration in
    match EConstr.kind sigma concl with
    | Prod (id0, t, b) -> unsafe_intro env (LocalAssum ({id0 with binder_name=id}, t)) ~relevance b
    | LetIn (id0, c, t, b) -> unsafe_intro env (LocalDef ({id0 with binder_name=id}, c, t)) ~relevance b
    | _ -> raise (RefinerError (env, sigma, IntroNeedsProduct))
  end


let build_intro_tac id dest tac = match dest with
  | MoveLast -> Tacticals.tclTHEN (introduction id) (tac id)
  | dest -> Tacticals.tclTHENLIST
    [introduction id; move_hyp id dest; tac id]

let rec intro_then_gen name_flag move_flag ~force ~dep tac =
  let open Context.Rel.Declaration in
  Proofview.Goal.enter begin fun gl ->
    let sigma = Tacmach.project gl in
    let env = Tacmach.pf_env gl in
    let concl = Proofview.Goal.concl gl in
    match EConstr.kind sigma concl with
    | Prod (name,t,u) when not dep || not (noccurn sigma 1 u) ->
        let name = find_name (LocalAssum (name,t)) name_flag gl in
        build_intro_tac name move_flag tac
    | LetIn (name,b,t,u) when not dep || not (noccurn sigma 1 u) ->
        let name = find_name (LocalDef (name,b,t)) name_flag gl in
        build_intro_tac name move_flag tac
    | Evar ev when force ->
        let name = find_name (LocalAssum (anonR,concl)) name_flag gl in
        let sigma, t = Evardefine.define_evar_as_product env sigma ~name ev in
        Tacticals.tclTHEN
          (Proofview.Unsafe.tclEVARS sigma)
          (intro_then_gen name_flag move_flag ~force ~dep tac)
    | _ ->
        begin if not force
          then
            let info = Exninfo.reify () in
            Proofview.tclZERO ~info (RefinerError (env, sigma, IntroNeedsProduct))
            (* Note: red_in_concl includes betaiotazeta and this was like *)
            (* this since at least V6.3 (a pity *)
            (* that intro do betaiotazeta only when reduction is needed; and *)
            (* probably also a pity that intro does zeta *)
          else Proofview.tclUNIT ()
        end <*>
          Proofview.tclORELSE
          (Tacticals.tclTHEN (hnf None)
             (intro_then_gen name_flag move_flag ~force:false ~dep tac))
          begin function (e, info) -> match e with
            | RefinerError (env, sigma, IntroNeedsProduct) ->
              Tacticals.tclZEROMSG ~info (str "No product even after head-reduction.")
            | e -> Proofview.tclZERO ~info e
          end
  end

let intro ?(move = MoveLast) ?(force = false) ?(dep = false)
  ?(tac = fun _ -> Proofview.tclUNIT ()) ?(naming = NamingAvoid Id.Set.empty) () =
  intro_then_gen naming move ~force ~dep tac

let intro_mustbe ?(move = MoveLast) ?(force = false) ?(dep = false)
  ?(tac = fun _ -> Proofview.tclUNIT ()) id =
  intro_then_gen (NamingMustBe (CAst.make id)) move ~force ~dep tac

let intro_basedon ?(move = MoveLast) ?(force = false) ?(dep = false)
  ?(tac = fun _ -> Proofview.tclUNIT ()) id =
  intro_then_gen (NamingBasedOn (id, Id.Set.empty)) move ~force ~dep tac

(**** Multiple introduction tactics ****)

let rec intros_mustbe ?(force = false) = function
  | []     -> Proofview.tclUNIT()
  | str::l -> Tacticals.tclTHEN (intro_mustbe ~force str) (intros_mustbe ~force l)

let rec intros_basedon_helper force tac acc = function
  | []     -> tac (List.rev acc)
  | str::l -> intro_basedon str ~force ~tac:(fun str' -> intros_basedon_helper force tac (str'::acc) l)

let intros_basedon ?(force = false) ?(tac = fun _ -> Proofview.tclUNIT ()) l =
  intros_basedon_helper force tac [] l

let is_overbound bound n = match bound with None -> false | Some p -> n >= p

let intro_forthcoming_last_then_gen avoid dep_flag bound n tac =
  let open RelDecl in
  Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    let concl = Proofview.Goal.concl gl in
    let relevance = Proofview.Goal.relevance gl in
    let avoid =
      let avoid' = ids_of_named_context_val (named_context_val env) in
      if Id.Set.is_empty avoid then avoid' else Id.Set.union avoid' avoid
    in
    let rec decompose env avoid n concl subst decls ndecls =
      let decl =
        if is_overbound bound n then None
        else match EConstr.kind sigma concl with
        | Prod (na, t, u) when not dep_flag || not (noccurn sigma 1 u) ->
          Some (LocalAssum (na, t), u)
        | LetIn (na, b, t, u) when not dep_flag || not (noccurn sigma 1 u) ->
          Some (LocalDef (na, b, t), u)
        | _ -> None
      in
      match decl with
      | None -> ndecls, decls, Vars.esubst Vars.lift_substituend subst concl
      | Some (decl, concl) ->
        let id = default_id env sigma decl in
        let id = next_ident_away_in_goal (Global.env ()) id avoid in
        let avoid = Id.Set.add id avoid in
        let env = EConstr.push_rel decl env in
        let ndecl = NamedDecl.of_rel_decl (fun _ -> id) decl in
        let ndecl = NamedDecl.map_constr (fun c -> Vars.esubst Vars.lift_substituend subst c) ndecl in
        let subst = Esubst.subs_cons (make_substituend @@ mkVar id) subst in
        decompose env avoid (n + 1) concl subst (decl :: decls) (ndecl :: ndecls)
    in
    let (ndecls, decls, nconcl) = decompose env avoid n concl (Esubst.subs_id 0) [] [] in
    let ids = List.map NamedDecl.get_id ndecls in
    if List.is_empty ids then tac []
    else Refine.refine_with_principal ~typecheck:false begin fun sigma ->
      let ctx = named_context_val env in
      let nctx = List.fold_right push_named_context_val ndecls ctx in
      let inst = SList.defaultn (List.length @@ Environ.named_context env) SList.empty in
      let rels = List.init (List.length decls) (fun i -> mkRel (i + 1)) in
      let ninst = List.fold_right (fun c accu -> SList.cons c accu) rels inst in
      let (sigma, ev) = new_pure_evar nctx sigma ~relevance nconcl in
      (sigma, it_mkLambda_or_LetIn (mkEvar (ev, ninst)) decls,
       Some ev)
    end <*> tac ids
  end

let intros =
  intro_forthcoming_last_then_gen Id.Set.empty false None 0 (fun _ -> tclIDTAC)

let rec intros_clearing = function
  | []          -> Proofview.tclUNIT ()
  | (false::tl) -> Tacticals.tclTHEN (intro ()) (intros_clearing tl)
  | (true::tl)  ->
      Tacticals.tclTHENLIST
        [ intro (); Tacticals.onLastHypId (fun id -> clear [id]); intros_clearing tl]

let intro_forthcoming_then_gen avoid move_flag ~dep bound n tac = match move_flag with
| MoveLast ->
  (* Fast path *)
  intro_forthcoming_last_then_gen avoid dep bound n tac
| MoveFirst | MoveAfter _ | MoveBefore _ ->
  let rec aux n ids =
    (* Note: we always use the bound when there is one for "*" and "**" *)
    if not (is_overbound bound n) then
    Proofview.tclORELSE
      begin
      intro_then_gen (NamingAvoid avoid) move_flag ~force:false ~dep
         (fun id -> aux (n+1) (id::ids))
      end
      begin function (e, info) -> match e with
      | RefinerError (env, sigma, IntroNeedsProduct) ->
          tac ids
      | e -> Proofview.tclZERO ~info e
      end
    else
      tac ids
  in
  aux n []

let intro_forthcoming avoid ?(move = MoveLast) ?(dep = false)
  ?(bound = None) ?(start = 0) ?(tac = fun _ -> Proofview.tclUNIT ()) () =
  intro_forthcoming_then_gen avoid move ~dep bound start tac

let clear_for_replacing ids =
  let fail env sigma id err inglobal =
    Loc.raise (ReplacingDependency (env, sigma, id, err, inglobal))
  in
  clear ~fail ids

let intro_replacing id =
  Proofview.Goal.enter begin fun gl ->
  let env, sigma = Proofview.Goal.(env gl, sigma gl) in
  let hyps = Proofview.Goal.hyps gl in
  let next_hyp = get_next_hyp_position env sigma id hyps in
  Tacticals.tclTHENLIST [
    clear_for_replacing [id];
    introduction id;
    move_hyp id next_hyp;
  ]
  end

(* We have e.g. [x, y, y', x', y'' |- forall y y' y'', G] and want to
   reintroduce y, y,' y''. Note that we have to clear y, y' and y''
   before introducing y because y' or y'' can e.g. depend on old y. *)

(* This version assumes that replacement is actually possible *)
(* (ids given in the introduction order) *)
(* We keep a sub-optimality in cleaing for compatibility with *)
(* the behavior of inversion *)
let intros_possibly_replacing ids =
  let suboptimal = true in
  Proofview.Goal.enter begin fun gl ->
    let env, sigma = Proofview.Goal.(env gl, sigma gl) in
    let hyps = Proofview.Goal.hyps gl in
    let posl = List.map (fun id -> (id, get_next_hyp_position env sigma id hyps)) ids in
    Tacticals.tclTHEN
      (Tacticals.tclMAP (fun id ->
        Tacticals.tclTRY (clear_for_replacing [id]))
         (if suboptimal then ids else List.rev ids))
      (Tacticals.tclMAP (fun (id,pos) ->
        Tacticals.tclORELSE (intro_mustbe id ~move:pos ~force:true) (intro_basedon id))
         posl)
  end

(* This version assumes that replacement is actually possible *)
let intros_replacing ids =
  Proofview.Goal.enter begin fun gl ->
    let hyps = Proofview.Goal.hyps gl in
    let env, sigma = Proofview.Goal.(env gl, sigma gl) in
    let posl = List.map (fun id -> (id, get_next_hyp_position env sigma id hyps)) ids in
    Tacticals.tclTHEN
      (clear_for_replacing ids)
      (Tacticals.tclMAP (fun (id,pos) -> intro_mustbe id ~move:pos ~force:true) posl)
  end

(* The standard for implementing Automatic Introduction *)
let auto_intros_tac ids =
  let fold used = function
    | Name id -> Id.Set.add id used
    | Anonymous -> used
  in
  let avoid = NamingAvoid (List.fold_left fold Id.Set.empty ids) in
  let naming = function
    | Name id -> NamingMustBe CAst.(make id)
    | Anonymous -> avoid
  in
  Tacticals.tclMAP (fun name -> intro ~naming:(naming name) ~force:true ()) (List.rev ids)

(* User-level introduction tactics *)

let lookup_hypothesis_as_renamed env sigma ccl = function
  | AnonHyp n -> Detyping.lookup_index_as_renamed env sigma ccl n
  | NamedHyp id -> Detyping.lookup_name_as_displayed env sigma ccl id.CAst.v

let lookup_hypothesis_as_renamed_gen red h gl =
  let env = Proofview.Goal.env gl in
  let rec aux ccl =
    match lookup_hypothesis_as_renamed env (Tacmach.project gl) ccl h with
      | None when red ->
        begin match red_product env (Proofview.Goal.sigma gl) ccl with
        | None -> None
        | Some c -> aux c
        end
      | x -> x
  in
  aux (Proofview.Goal.concl gl)

let is_quantified_hypothesis id gl =
  match lookup_hypothesis_as_renamed_gen false (NamedHyp (CAst.make id)) gl with
    | Some _ -> true
    | None -> false

let warn_deprecated_intros_until_0 =
  CWarnings.create ~name:"deprecated-intros-until-0" ~category:CWarnings.CoreCategories.tactics
    (fun () ->
       strbrk"\"intros until 0\" is deprecated, use \"intros *\"; instead of \"induction 0\" and \"destruct 0\" use explicitly a name.\"")

let depth_of_quantified_hypothesis red h gl =
  if h = AnonHyp 0 then warn_deprecated_intros_until_0 ();
  match lookup_hypothesis_as_renamed_gen red h gl with
    | Some depth -> depth
    | None -> Loc.raise (NoQuantifiedHypothesis(h,red))

let intros_until_gen red h =
  Proofview.Goal.enter begin fun gl ->
    let n = depth_of_quantified_hypothesis red h gl in
    Tacticals.tclDO n (intro ~force:red ())
  end

let intros_until_id id = intros_until_gen false (NamedHyp (CAst.make id))

let intros_until = intros_until_gen true

let tclCHECKVAR id =
  Proofview.Goal.enter begin fun gl ->
    let _ = Tacmach.pf_get_hyp id gl in
    Proofview.tclUNIT ()
  end

let try_intros_until_id_check id =
  Tacticals.tclORELSE (intros_until_id id) (tclCHECKVAR id)

let try_intros_until tac = function
  | NamedHyp {CAst.v=id} -> Tacticals.tclTHEN (try_intros_until_id_check id) (tac id)
  | AnonHyp n -> Tacticals.tclTHEN (intros_until (AnonHyp n)) (Tacticals.onLastHypId tac)

let rec intros_move = function
  | [] -> Proofview.tclUNIT ()
  | (hyp,destopt) :: rest ->
      Tacticals.tclTHEN (intro_mustbe hyp ~move:destopt)
        (intros_move rest)
