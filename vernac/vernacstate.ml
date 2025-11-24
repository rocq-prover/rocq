(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module Synterp = struct

  type t = Lib.Synterp.frozen * Summary.Synterp.frozen

  let freeze sum =
    (Lib.Synterp.freeze (), Summary.Synterp.freeze_summaries sum)

  let unfreeze sum (fl,fs) =
    Lib.Synterp.unfreeze fl;
    Summary.Synterp.unfreeze_summaries fs sum

  let parsing (_fl, fs) =
    Summary.Synterp.project_from_summary fs Procq.parser_summary_tag

  module Stm = struct
    let make_shallow (lib, summary) = Lib.Synterp.drop_objects lib, summary
    let lib = fst
    let summary = snd
  end

end

module Interp_system : sig
  type t
  val freeze : Summary.Interp.t -> t
  val unfreeze : Summary.Interp.mut -> t -> unit
  module Stm : sig
    val make_shallow : t -> t
    val lib : t -> Lib.Interp.frozen
    val summary : t -> Summary.Interp.frozen
    val replace_summary : t -> Summary.Interp.frozen -> t
  end

end = struct

  type t = Lib.Interp.frozen * Summary.Interp.frozen

  let freeze sum =
    (Lib.Interp.freeze (), Summary.Interp.freeze_summaries sum)

  let unfreeze sum (fl,fs) =
    Lib.Interp.unfreeze fl;
    Summary.Interp.unfreeze_summaries fs sum

  module Stm = struct
    let make_shallow (lib, summary) = Lib.Interp.drop_objects lib, summary
    let lib = fst
    let summary = snd
    let replace_summary (lib,_) summary = (lib,summary)
  end
end

module System = struct
let protect f sum =
  let freeze () = let s = Synterp.freeze sum.Summary.Interp.synterp in let i = Interp_system.freeze sum in s, i in
  let sum = ref sum in
  let unfreeze (s,i) =
    Summary.run_synterp_interp
      (fun sum -> Synterp.unfreeze sum s)
      (fun sum () -> Interp_system.unfreeze sum i)
      sum
  in
  let open Memprof_coq.Resource_bind in
  let& () = Util.protect_state ~freeze ~unfreeze in
  f sum
end

module LemmaStack = struct

  type t = Declare.Proof.t NeList.t

  let map ~f x = NeList.map f x
  let map_top ~f x = NeList.map_head f x

  let pop x = NeList.head x, NeList.tail x

  let get_top = NeList.head
  let with_top x ~f = f (get_top x)

  let push ontop a = NeList.push a ontop

  let get_all_proof_names (pf : t) =
    let prj x = Declare.Proof.get x in
    List.map Proof.(function pf -> (data (prj pf)).name) (NeList.to_list pf)

  let copy_info src tgt =
    Declare.Proof.map ~f:(fun _ -> Declare.Proof.get tgt) src

  let copy_info ~(src : t) ~(tgt : t) =
    NeList.map2 copy_info src tgt

end

let s_cache = ref None
let s_lemmas = ref None
let s_program = ref (NeList.singleton Declare.OblState.empty)

module Interp = struct

module System = Interp_system

type t = {
  system  : System.t;              (* summary + libstack *)
  lemmas  : LemmaStack.t option;   (* proofs of lemmas currently opened *)
  program : Declare.OblState.t NeList.t;    (* obligations table *)
  opaques : Opaques.Summary.t;     (* opaque proof terms *)
}

let invalidate_cache () =
  s_cache := None

let update_cache rf v =
  rf := Some v; v

let do_if_not_cached rf f v =
  match !rf with
  | Some fr when fr == v -> ()
  | _ ->
    let () = f v in
    rf := Some v

let freeze_interp_state sum =
  { system = update_cache s_cache (System.freeze sum);
    lemmas = !s_lemmas;
    program = !s_program;
    opaques = Opaques.Summary.freeze ();
  }

let make_shallow s =
  { s with system = System.Stm.make_shallow s.system }

let unfreeze_interp_state sum { system; lemmas; program; opaques } =
  let sum = do_if_not_cached s_cache (System.unfreeze sum) system in
  s_lemmas := lemmas;
  s_program := program;
  Opaques.Summary.unfreeze opaques;
  sum

end

type t =
  { synterp: Synterp.t
  ; interp: Interp.t
  }

let freeze_full_state sum =
  { synterp = Synterp.freeze sum.Summary.Interp.synterp;
    interp = Interp.freeze_interp_state sum;
  }

let unfreeze_full_state sum st =
  NewProfile.profile "unfreeze_full_state" (fun () ->
      Summary.run_synterp_interp
        (fun sum -> Synterp.unfreeze sum st.synterp)
        (fun sum () -> Interp.unfreeze_interp_state sum st.interp)
        sum)
    ()

(* Compatibility module *)
module Declare_ = struct

  let get_program () = !s_program

  let set (pstate,pm) =
    s_lemmas := pstate;
    s_program := pm

  let get_pstate () =
    Option.map (LemmaStack.with_top ~f:(fun x -> x)) !s_lemmas

  let unfreeze x = s_lemmas := Some x

  exception NoCurrentProof

  let () =
    CErrors.register_handler begin function
      | NoCurrentProof ->
        Some (Pp.(str "No focused proof (No proof-editing in progress)."))
      | _ -> None
    end

  let cc f = match !s_lemmas with
    | None -> raise NoCurrentProof
    | Some x -> LemmaStack.with_top ~f x

  let cc_stack f = match !s_lemmas with
    | None -> raise NoCurrentProof
    | Some x -> f x

  let dd f = match !s_lemmas with
    | None -> raise NoCurrentProof
    | Some x -> s_lemmas := Some (LemmaStack.map_top ~f x)

  let there_are_pending_proofs () = !s_lemmas <> None
  let get_open_goals () = cc Declare.Proof.get_open_goals

  let give_me_the_proof_opt () = Option.map (LemmaStack.with_top ~f:Declare.Proof.get) !s_lemmas
  let give_me_the_proof () = cc Declare.Proof.get
  let get_current_proof_name () = cc Declare.Proof.get_name

  let map_proof f = dd (Declare.Proof.map ~f)
  let with_current_proof f =
    match !s_lemmas with
    | None -> raise NoCurrentProof
    | Some stack ->
      let pf, res = LemmaStack.with_top stack ~f:(Declare.Proof.map_fold ~f) in
      let stack = LemmaStack.map_top stack ~f:(fun _ -> pf) in
      s_lemmas := Some stack;
      res

  let return_proof () = cc Declare.Proof.return_proof

  let close_future_proof ~feedback_id pf =
    NewProfile.profile "close_future_proof" (fun () ->
        cc (fun pt -> Declare.Proof.close_future_proof ~feedback_id pt pf))
      ()

  let close_proof ~opaque ~keep_body_ucst_separate =
    NewProfile.profile "close_proof" (fun () ->
        cc (fun pt -> Declare.Proof.close_proof ~opaque ~keep_body_ucst_separate pt))
      ()

  let discard_all () = s_lemmas := None
  let update_sigma_univs ugraph = dd (Declare.Proof.update_sigma_univs ugraph)

  let get_current_context () = cc Declare.Proof.get_current_context

  let get_all_proof_names () =
    try cc_stack LemmaStack.get_all_proof_names
    with NoCurrentProof -> []

  let copy_terminators ~src ~tgt =
    match src, tgt with
    | None, None -> None
    | Some _ , None -> None
    | None, Some x -> Some x
    | Some src, Some tgt -> Some (LemmaStack.copy_info ~src ~tgt)

end

(* STM-specific state-handling *)
module Stm = struct

  (* Proof-related state, for workers; ideally the two counters would
     be contained in the lemmas state themselves, as there is no need
     for evar / metas to be global among proofs *)
  type nonrec pstate =
    LemmaStack.t option *
    int *                                   (* Evarutil.meta_counter_summary_tag *)
    int                                     (* Evd.evar_counter_summary_tag *)

  (* Parts of the system state that are morally part of the proof state *)
  let pstate { interp = { lemmas; system }} =
    let st = Interp.System.Stm.summary system in
    lemmas,
    Summary.Interp.project_from_summary st Evarutil.meta_counter_summary_tag,
    Summary.Interp.project_from_summary st Evd.evar_counter_summary_tag

  let set_pstate ({ interp = { lemmas; system } } as s) (pstate,c1,c2) =
    { s with interp = { s.interp with
      lemmas =
        Declare_.copy_terminators ~src:s.interp.lemmas ~tgt:pstate
    ; system =
        Interp.System.Stm.replace_summary s.interp.system
          begin
            let st = Interp.System.Stm.summary s.interp.system in
            let st = Summary.Interp.modify_summary st Evarutil.meta_counter_summary_tag c1 in
            let st = Summary.Interp.modify_summary st Evd.evar_counter_summary_tag c2 in
            st
          end
      }
    }

  type non_pstate = Summary.Synterp.frozen * Lib.Synterp.frozen * Summary.Interp.frozen * Lib.Interp.frozen
  let non_pstate { synterp; interp } =
    let system = interp.system in
    let st = Interp.System.Stm.summary system in
    let st = Summary.Interp.remove_from_summary st Evarutil.meta_counter_summary_tag in
    let st = Summary.Interp.remove_from_summary st Evd.evar_counter_summary_tag in
    Synterp.Stm.summary synterp, Synterp.Stm.lib synterp,
      st, Interp.System.Stm.lib system

  let unfreeze_non_pstate cur_summary (s_synterp,l_synterp,s_interp,l_interp) =
    let evar_cnt = Evd.Internal.current_evar_counter() in
    let s_interp = Summary.Interp.modify_summary s_interp Evd.evar_counter_summary_tag evar_cnt in
    let s_interp = Summary.Interp.modify_summary s_interp Evarutil.meta_counter_summary_tag (Evarutil.Internal.current_meta_counter()) in
    let () = Summary.run_synterp_interp
        (fun sum ->
           Summary.Synterp.unfreeze_summaries ~partial:true s_synterp sum;
           Lib.Synterp.unfreeze l_synterp)
        (fun sum () ->
           Summary.Interp.unfreeze_summaries ~partial:true s_interp sum;
           Lib.Interp.unfreeze l_interp)
        cur_summary
    in
    if Declare_.there_are_pending_proofs () then
      Declare_.update_sigma_univs (Global.universes ())

  let same_env { interp = { system = s1 } } { interp = { system = s2 } } =
    let s1 = Interp.System.Stm.summary s1 in
    let e1 = Summary.Interp.project_from_summary s1 Global.global_env_summary_tag in
    let s2 = Interp.System.Stm.summary s2 in
    let e2 = Summary.Interp.project_from_summary s2 Global.global_env_summary_tag in
    e1 == e2

  let make_shallow st =
    { interp = Interp.make_shallow st.interp
    ; synterp = Synterp.Stm.make_shallow st.synterp
    }

end
module Declare = Declare_
