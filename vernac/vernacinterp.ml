(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Vernacexpr
open Synterp

let vernac_pperr_endline = CDebug.create ~name:"vernacinterp" ()

let real_error_loc ~cmdloc ~eloc =
  if Loc.finer eloc cmdloc then eloc
  else cmdloc

let locate_if_not_already ?loc (e, info) =
  (e, Option.cata (Loc.add_loc info) info (real_error_loc ~cmdloc:loc ~eloc:(Loc.get_loc info)))

let unfreeze_local_synterp sum synterp =
  let synterp, () =
    Summary.Synterp.with_mut (fun sum -> Vernacstate.Synterp.unfreeze sum synterp)
      sum.Summary.Interp.synterp
  in
  { sum with synterp }

let with_interp_state ~unfreeze_transient st =
  let with_local_state synterp_st f sum =
    let sum = unfreeze_transient sum synterp_st in
    let v = f sum in
    Vernacstate.Interp.invalidate_cache ();
    let sum = unfreeze_local_synterp sum st.Vernacstate.synterp in
    Vernacstate.Interp.unfreeze_interp_state sum st.Vernacstate.interp;
    (), v
  in
  { VernacControl.with_local_state }

let interp_control_gen ~loc ~st ~unfreeze_transient control f sum =
  let noop = st.Vernacstate.interp.lemmas, st.Vernacstate.interp.program in
  let control, res =
    VernacControl.under_control ~loc
      ~with_local_state:(with_interp_state ~unfreeze_transient st)
      control
      ~noop
      (Flags.with_modified_ref Flags.in_synterp_phase (fun _ -> Some false) f)
      sum
  in
  if VernacControl.after_last_phase ~loc control
  then noop
  else res

(* [loc] is the [Loc.t] of the vernacular command being interpreted. *)
let rec interp_expr sum ?loc ~st cmd =
  let before_univs = Global.universes () in
  let pstack, pm = with_generic_atts ~check:false cmd.attrs (fun ~atts ->
      interp_expr_core sum ?loc ~atts ~st cmd.expr)
  in
  let after_univs = Global.universes () in
  if before_univs == after_univs then pstack, pm
  else
    let f = Declare.Proof.update_sigma_univs after_univs in
    Option.map (Vernacstate.LemmaStack.map ~f) pstack, pm

and interp_expr_core sum ?loc ~atts ~st c =
  match c with

  (* The STM should handle that, but LOAD bypasses the STM... *)
  | VernacSynPure VernacAbortAll    -> CErrors.user_err (Pp.str "AbortAll cannot be used through the Load command")
  | VernacSynPure VernacRestart     -> CErrors.user_err (Pp.str "Restart cannot be used through the Load command")
  | VernacSynPure VernacUndo _      -> CErrors.user_err (Pp.str "Undo cannot be used through the Load command")
  | VernacSynPure VernacUndoTo _    -> CErrors.user_err (Pp.str "UndoTo cannot be used through the Load command")

  (* Resetting *)
  | VernacSynPure VernacResetName _  -> CErrors.anomaly (Pp.str "VernacResetName not handled by Stm.")
  | VernacSynPure VernacResetInitial -> CErrors.anomaly (Pp.str "VernacResetInitial not handled by Stm.")
  | VernacSynPure VernacBack _       -> CErrors.anomaly (Pp.str "VernacBack not handled by Stm.")

  | VernacSynterp EVernacLoad (verbosely, fname) ->
    Attributes.unsupported_attributes atts;
    vernac_load sum ~verbosely fname

  | v ->
    let fv = Vernacentries.translate_vernac ?loc ~atts v in
    let stack = st.Vernacstate.interp.lemmas in
    let program = st.Vernacstate.interp.program in
    let {Vernactypes.prog; proof; opaque_access=(); }, () = Vernactypes.run fv {
        prog=program;
        proof=stack;
        opaque_access=();
      }
      sum
    in
    proof, prog

and vernac_load sum ~verbosely entries =
  (* Note that no proof should be open here, so the state here is just token for now *)
  let st = Vernacstate.freeze_full_state (Summary.Interp.get sum) in
  let v_mod = if verbosely then Flags.verbosely else Flags.silently in
  let interp_entry (stack, pm) (CAst.{ loc; v = cmd }, synterp_st) =
    let sum = unfreeze_local_synterp sum synterp_st in
    let st = Vernacstate.{ synterp = synterp_st; interp = { st.interp with Interp.lemmas = stack; program = pm }} in
    v_mod (interp_control sum ~st) (CAst.make ?loc cmd)
  in
  let pm = st.Vernacstate.interp.program in
  let stack = st.Vernacstate.interp.lemmas in
  let stack, pm =
    Dumpglob.with_glob_output Dumpglob.NoGlob
    (fun () -> List.fold_left interp_entry (stack, pm) entries) ()
  in
  (* If Load left a proof open, we fail too. *)
  if Option.has_some stack then
    CErrors.user_err Pp.(str "Files processed by Load cannot leave open proofs.");
  stack, pm

and interp_control sum ~st ({ CAst.v = cmd; loc }) =
  Util.try_finally (fun () ->
      Loc.set_current_command_loc loc;
      interp_control_gen ~loc ~st cmd.control
        ~unfreeze_transient:unfreeze_local_synterp
        (fun sum -> interp_expr sum ?loc ~st cmd)
        sum)
    ()
    (fun () -> Loc.set_current_command_loc None)
    ()

(* XXX: This won't properly set the proof mode, as of today, it is
   controlled by the STM. Thus, we would need access information from
   the classifier. The proper fix is to move it to the STM, however,
   the way the proof mode is set there makes the task non trivial
   without a considerable amount of refactoring.
*)

(* Interpreting a possibly delayed proof *)
let interp_qed_delayed ~proof ~st sum pe =
  let stack = st.Vernacstate.interp.lemmas in
  let pm = st.Vernacstate.interp.program in
  let stack = Option.cata (fun stack -> snd @@ Vernacstate.LemmaStack.pop stack) None stack in
  let pm = NeList.map_head (fun pm -> match pe with
      | Admitted ->
        Declare.Proof.save_lemma_admitted_delayed sum ~pm ~proof
      | Proved (_,idopt) ->
        let pm = Declare.Proof.save_lemma_proved_delayed sum ~pm ~proof ~idopt in
        pm)
      pm
  in
  stack, pm

let interp_qed_delayed_control ~proof sum ~st ~control { CAst.loc; v=pe } =
  interp_control_gen ~loc ~st control
    ~unfreeze_transient:(fun sum () -> sum)
    (fun sum -> interp_qed_delayed ~proof ~st sum pe)
    sum

(* General interp with management of state *)

(* Be careful with the cache here in case of an exception. *)
let interp_gen ~verbosely ~st ~interp_fn sum cmd =
  try
    let v_mod = if verbosely then Flags.verbosely else Flags.silently in
    let ontop = v_mod (interp_fn sum ~st) cmd in
    Vernacstate.Declare.set ontop [@ocaml.warning "-3"];
    Vernacstate.Interp.freeze_interp_state (Summary.Interp.get sum)
  with exn ->
    let exn = Exninfo.capture exn in
    let exn = locate_if_not_already ?loc:cmd.CAst.loc exn in
    Vernacstate.Interp.invalidate_cache ();
    Exninfo.iraise exn

(* Regular interp *)
let interp ~intern ?(verbosely=true) ~st sum cmd =
  let () = Vernacstate.unfreeze_full_state sum st in
  vernac_pperr_endline Pp.(fun () -> str "interpreting: " ++ Ppvernac.pr_vernac_expr cmd.CAst.v.expr);
  let interp =
    Summary.run_synterp_interp
      (fun sum ->
         NewProfile.profile "synterp" (fun () ->
             Synterp.synterp_control sum ~intern cmd) ())
      (fun sum entry ->
         NewProfile.profile "interp" (fun () ->
             interp_gen ~verbosely ~st ~interp_fn:interp_control sum entry) ())
      sum
  in
  (* XXX freeze synterp between synterp and interp phases? should be equivalent *)
  Vernacstate.{ synterp = Vernacstate.Synterp.freeze !sum.synterp; interp }

let interp_entry ?(verbosely=true) sum ~st entry =
  let () = Vernacstate.unfreeze_full_state sum st in
  Summary.run_interp (fun sum ->
      interp_gen ~verbosely ~st ~interp_fn:interp_control sum entry)
    sum

module Intern = struct

  let fs_intern dp =
    match Loadpath.locate_absolute_library dp with
    | Ok file ->
      Feedback.feedback @@ Feedback.FileDependency (Some file, Names.DirPath.to_string dp);
      let res, provenance = Library.intern_from_file file in
      Result.iter (fun _ ->
          Feedback.feedback @@ Feedback.FileLoaded (Names.DirPath.to_string dp, file)) res;
      res, provenance
    | Error e ->
      Loadpath.Error.raise dp e
end

let fs_intern = Intern.fs_intern

let interp_qed_delayed_proof ~proof ~st ~control sum (CAst.{loc; v = pe } as e) : Vernacstate.Interp.t =
  NewProfile.profile "interp-delayed-qed" (fun () ->
      interp_gen ~verbosely:false ~st
        ~interp_fn:(interp_qed_delayed_control ~proof ~control) sum e)
    ()
