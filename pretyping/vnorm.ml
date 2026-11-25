(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let context sigma =
  let evar_type evk =
    let evi = Evd.find_undefined sigma evk in
    let hyps = EConstr.named_context_of_val (Evd.evar_filtered_hyps evi) in
    (* The VM passes let-bound arguments as well as assumptions. *)
    let hyps = Context.Named.drop_bodies hyps in
    let typ = List.fold_left (fun t d -> EConstr.mkNamedProd_or_LetIn sigma d t)
        (Evd.evar_concl evi) hyps in
    List.length hyps, EConstr.to_constr ~abort_on_undefined_evars:false sigma typ
  in
  let return_is_relevant _ = function
  | Sorts.Relevant -> true
  | Sorts.Irrelevant -> false
  | Sorts.RelevanceVar q -> UState.is_above_prop (Evd.ustate sigma) q
  in
  { Vreadback.evars = Evd.evar_handler sigma; evar_type; return_is_relevant }

type vm_flags = {
  vm_normalize_params : bool;
  vm_share_values : bool;
}

let default_vm_flags = {
  vm_normalize_params = false;
  vm_share_values = true;
}

let cbv_vm ?(flags = default_vm_flags) env sigma c t  =
  if not (Environ.typing_flags env).enable_VM then
    CErrors.user_err Pp.(str "vm_compute reduction has been disabled.");
  if Termops.occur_meta sigma c then
    CErrors.user_err Pp.(str "vm_compute does not support metas.");
  (* This evar-normalizes terms beforehand *)
  let c = EConstr.Unsafe.to_constr c in
  let t = EConstr.Unsafe.to_constr t in
  let share = flags.vm_share_values in
  let ctx = context sigma in
  let v = Vmsymtable.val_of_constr ~share env { Genlambda.evars_val = ctx.evars } c in
  let env = Environ.set_universes (Evd.universes sigma) env in
  EConstr.of_constr (Vreadback.readback ~normalize_params:flags.vm_normalize_params env ctx v t)
