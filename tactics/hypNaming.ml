(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Environ
open EConstr
open Namegen
open Logic
open TacticExceptions
open Goptions

module NamedDecl = Context.Named.Declaration

(**************************************************************)
(** Default clear flag.                                       *)
(**************************************************************)

let clear_hyp_by_default = ref false

let () =
  declare_bool_option
    { optstage = Summary.Stage.Interp;
      optdepr  = None;
      optkey   = ["Default"; "Clearing"; "Used"; "Hypotheses"];
      optread  = (fun () -> !clear_hyp_by_default) ;
      optwrite = (fun b -> clear_hyp_by_default := b) }

let use_clear_hyp_by_default () = !clear_hyp_by_default

let apply_clear_request clear_flag dft c =
  let doclear = match clear_flag with
    | None -> if dft then c else None
    | Some true ->
      begin match c with
      | None -> Loc.raise KeepAndClearModifierOnlyForHypotheses
      | Some id -> Some id
      end
    | Some false -> None
  in
  match doclear with
  | None -> Proofview.tclUNIT ()
  | Some id -> ContextTactics.clear [id]

(**************************************************************)
(** Fresh name generation.                                    *)
(**************************************************************)

let fresh_id_in_env avoid id env =
  let avoid' = ids_of_named_context_val (named_context_val env) in
  let avoid = if Id.Set.is_empty avoid then avoid' else Id.Set.union avoid' avoid in
  next_ident_away_in_goal (Global.env ()) id avoid

let id_of_name_with_default id = function
  | Anonymous -> id
  | Name id   -> id

let default_id_of_sort sigma s =
  if ESorts.is_small sigma s then default_small_ident else default_type_ident

let default_id env sigma decl =
  let open Context.Rel.Declaration in
  match decl with
  | LocalAssum (name,t) ->
      let dft = default_id_of_sort sigma (Retyping.get_sort_of env sigma t) in
      id_of_name_with_default dft name.binder_name
  | LocalDef (name,b,_) -> id_of_name_using_hdchar env sigma b name.binder_name

(**************************************************************)
(** Naming introduced hypotheses.                             *)
(**************************************************************)

type name_flag =
  | NamingAvoid of Id.Set.t
  | NamingBasedOn of Id.t * Id.Set.t
  | NamingMustBe of lident

let naming_of_name = function
  | Anonymous -> NamingAvoid Id.Set.empty
  | Name id -> NamingMustBe (CAst.make id)

let find_name ?(replace = false) decl naming gl = match naming with
  | NamingAvoid idl ->
      (* This case must be compatible with [find_intro_names] below. *)
      let env = Proofview.Goal.env gl in
      let sigma = Tacmach.project gl in
      fresh_id_in_env idl (default_id env sigma decl) (Proofview.Goal.env gl)
  | NamingBasedOn (id,idl) -> fresh_id_in_env idl id (Proofview.Goal.env gl)
  | NamingMustBe {CAst.loc;v=id} ->
     (* When name is given, we allow to hide a global name. *)
     let ids_of_hyps = Tacmach.pf_ids_set_of_hyps gl in
     if not replace && Id.Set.mem id ids_of_hyps then
       Loc.raise ?loc (AlreadyUsed id);
     id

(**************************************************************)
(** Computing position of hypotheses for replacing.           *)
(**************************************************************)

let get_next_hyp_position env sigma id =
  let rec aux = function
  | [] -> error_no_such_hypothesis env sigma id
  | decl :: right ->
    if Id.equal (NamedDecl.get_id decl) id then
      match right with decl::_ -> MoveBefore (NamedDecl.get_id decl) | [] -> MoveFirst
    else
      aux right
  in
  aux

let get_previous_hyp_position env sigma id =
  let rec aux dest = function
  | [] -> error_no_such_hypothesis env sigma id
  | decl :: right ->
      let hyp = NamedDecl.get_id decl in
      if Id.equal hyp id then dest else aux (MoveAfter hyp) right
  in
  aux MoveLast
