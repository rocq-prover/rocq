type hint = Hints.FullHint.t

(*
   Given a hint database name as a string, return the list of hints associated.
   To start, I'm ignoring head and the hint_mode options for now.
   We lose some information. Should be easy to add.
*)
let get_hints db_name = try
    let db = Hints.searchtable_map db_name in
    let dblist = Hints.Hint_db.fold (fun _ _ hl l -> hl @ l) db [] in
    Some dblist
    with Not_found -> None


(*
   To be more precise, we run hints exactly like auto does. There is some code
   duplication. It would be good to not have this..
   IMO, the right way is to have every tactic expose how they run a hint.
   The user can then get to choose.
   The API can then be run_hint <hint> <strat>
 *)
let run_hint hint =
    let open Hints in
    let open Auto in
    let open Locus in
    let open Locusops in
    let auto_flags = (Auto.auto_flags_of_state TransparentState.empty) in
    let unify_resolve_nodelta =  unify_resolve auto_flags in
    let helper = function
    | Res_pf h -> unify_resolve_nodelta h
    | ERes_pf _ -> let info = Exninfo.reify () in
        Tacticals.tclZEROMSG ~info (Pp.str "eres_pf")
    | Give_exact h  -> exact h
    | Res_pf_THEN_trivial_fail h ->
        Feedback.msg_notice (Pp.str "This is an immediate tactic");
        unify_resolve_nodelta h
    | Unfold_nth c -> Tactics.reduce (Unfold [AllOccurrences,c]) onConcl (* This is eauto-like. Just a strawman *)
    | Extern (p, tacast) -> Proofview.Goal.enter begin fun gl ->
        let concl = Proofview.Goal.concl gl in
        conclPattern concl p tacast
    end
  in Hints.FullHint.run hint helper
