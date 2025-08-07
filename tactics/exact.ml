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
open EConstr
open Reductionops
open Proofview.Notations
open ConvTactics

module NamedDecl = Context.Named.Declaration

let exact_no_check c =
  Refine.refine ~typecheck:false (fun h -> (h,c))

let exact_check c =
  Proofview.Goal.enter begin fun gl ->
  let sigma = Proofview.Goal.sigma gl in
  (* We do not need to normalize the goal because we just check convertibility *)
  let concl = Proofview.Goal.concl gl in
  let env = Proofview.Goal.env gl in
  let sigma, ct = Typing.type_of env sigma c in
  Tacticals.tclTHEN (Proofview.Unsafe.tclEVARS sigma)
  (Tacticals.tclTHEN (convert ~pb:Conversion.CUMUL ct concl) (exact_no_check c))
  end

let cast_no_check ~kind c =
  Proofview.Goal.enter begin fun gl ->
    let concl = Proofview.Goal.concl gl in
    exact_no_check (mkCast (c, kind, concl))
  end

let vm_cast_no_check c = cast_no_check ~kind:VMcast c

let native_cast_no_check c = cast_no_check ~kind:NATIVEcast c

let exact_proof c =
  let open Tacmach in
  Proofview.Goal.enter begin fun gl ->
  Refine.refine ~typecheck:false begin fun sigma ->
    Constrintern.interp_casted_constr_evars ~flags:Pretyping.all_and_fail_flags (pf_env gl) sigma c (pf_concl gl)
  end
  end

(** For efficiency reasons we first try to find a hypothesis whose type
    is syntactically equal to the goal. If this fails we retry with full conversion. *)
let assumption =
  let rec arec gl only_eq = function
  | [] ->
    if only_eq then
      let hyps = Proofview.Goal.hyps gl in
      arec gl false hyps
    else
      let info = Exninfo.reify () in
      Tacticals.tclZEROMSG ~info (str "No such assumption.")
  | decl::rest ->
    let t = NamedDecl.get_type decl in
    let concl = Proofview.Goal.concl gl in
    let sigma = Tacmach.project gl in
    let ans =
      if only_eq then
        if EConstr.eq_constr sigma t concl then Some sigma
        else None
      else
        let env = Proofview.Goal.env gl in
        infer_conv env sigma t concl
    in
    match ans with
    | Some sigma ->
      (Proofview.Unsafe.tclEVARS sigma) <*>
        exact_no_check (mkVar (NamedDecl.get_id decl))
    | None -> arec gl only_eq rest
  in
  let assumption_tac gl =
    let hyps = Proofview.Goal.hyps gl in
    arec gl true hyps
  in
  Proofview.Goal.enter assumption_tac
