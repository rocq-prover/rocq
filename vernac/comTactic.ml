(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Goptions

module Dyn = Dyn.Make()

module DMap = Dyn.Map(struct type 'a t = 'a -> unit Proofview.tactic end)

let interp_map = ref DMap.empty

type interpretable = I : 'a Dyn.tag * 'a -> interpretable
type 'a tactic_interpreter = Interpreter of ('a -> interpretable)

let register_tactic_interpreter na f =
  let t = Dyn.create na in
  interp_map := DMap.add t f !interp_map;
  Interpreter (fun x -> I (t,x))

let interp_tac (I (tag,t)) =
  let f = DMap.find tag !interp_map in
  f t

type parallel_solver =
  pstate:Declare.Proof.t ->
  info:int option ->
  interpretable ->
  abstract:bool ->
  Declare.Proof.t

let { Goptions.get = print_info_trace } =
  declare_intopt_option_and_ref
    ~key:["Info" ; "Level"]
    ~value:None
    ()

let warn_end_tac =
  CWarnings.create_warning ~name:"deprecated-end-tac" ~from:[Deprecation.Version.v9_2] ()

let pp_warn_end_tac =
  CWarnings.create_in warn_end_tac Pp.(fun pptac ->
      (* XXX we need to print eagerly for the quickfix but it should be delayed *)
      fmt "Using \"...\" is deprecated, use \"%t\" instead" (fun () -> pptac))

let warn_end_tac ?loc end_tac =
  match end_tac with
  | None -> CErrors.user_err ?loc Pp.(str "This \"...\" is useless, use \".\" instead.")
  | Some end_tac ->
  match CWarnings.warning_status warn_end_tac with
  | Disabled -> ()
  | _ ->
    let pptac =
      let env = Global.env() in
      let sigma = Evd.from_env env in
      let pptac = Gentactic.print_glob env sigma end_tac in
      Pp.(str ";" ++ spc() ++ pptac ++ str ".")
    in
    let qf = match loc with
      | None -> []
      | Some loc -> [Quickfix.make ~loc pptac]
    in
    pp_warn_end_tac ?loc ~quickfix:qf pptac

let use_end_tac ~with_end_tac end_tac =
  if not with_end_tac.CAst.v then None
  else begin
    warn_end_tac ?loc:with_end_tac.loc end_tac;
    Option.map Gentactic.interp end_tac
  end

let solve_core ~pstate n ~info ?(with_end_tac=CAst.make false) t =
  let pstate, status = Declare.Proof.map_fold_endline ~f:(fun etac p ->
      let with_end_tac = use_end_tac ~with_end_tac etac in
      let info = Option.append info (print_info_trace ()) in
      let (p,status) = Proof.solve (Global.env ()) n info t ?with_end_tac p in
      let p = Declare.Internal.register_side_effects p in
      (* in case a strict subtree was completed,
         go back to the top of the prooftree *)
      let p = Proof.maximal_unfocus Vernacentries.command_focus p in
      p,status) pstate in
  if not status then Feedback.feedback Feedback.AddedAxiom;
  pstate

let solve ~pstate n ~info ?with_end_tac t =
  let t = interp_tac t in
  solve_core ~pstate n ~info t ?with_end_tac

let check_par_applicable pstate =
  Declare.Proof.fold pstate ~f:(fun p ->
    (Proof.data p).Proof.goals |> List.iter (fun goal ->
    let is_ground =
      let { Proof.sigma = sigma0 } = Declare.Proof.fold pstate ~f:Proof.data in
      let g = Evd.find_undefined sigma0 goal in
      let concl, hyps = Evd.evar_concl g, Evd.evar_context g in
      Evarutil.is_ground_term sigma0 concl &&
      List.for_all (Context.Named.Declaration.for_all (Evarutil.is_ground_term sigma0)) hyps in
    if not is_ground then
      CErrors.user_err
        Pp.(strbrk("The par: goal selector does not support goals with existential variables"))))

let par_implementation : parallel_solver ref = ref (fun ~pstate ~info t ~abstract ->
  let t = interp_tac t in
  let t = Proofview.Goal.enter (fun _ ->
    if abstract then Abstract.tclABSTRACT None ~opaque:true t else t) 
  in
  solve_core ~pstate Goal_select.SelectAll ~info t)

let set_par_implementation f = par_implementation := f

let solve_parallel ~pstate ~info t ~abstract =
  check_par_applicable pstate;
  !par_implementation ~pstate ~info t ~abstract
