type hint_db = Hints.Hint_db.t
type hint = Hints.FullHint.t


(* Given a hint database name as a string, return an optional hint_db *)
let get_hint_db db_name = try Some (Hints.searchtable_map db_name) with Not_found -> None

(* Compute all applicable hints, given a hint database *)
let get_applicable_hints db =
  Proofview.Goal.enter_one begin fun gl ->
    let hint_lst =  try
      let sigma = Proofview.Goal.sigma gl in
      let concl = Proofview.Goal.concl gl in
      let hyps = Proofview.Goal.hyps gl in
      let secvars = Hints.secvars_of_hyps hyps in
      let hd, _ = Hints.decompose_app_bound sigma concl in
      Hints.Hint_db.map_all ~secvars hd db
    with Hints.Bound -> [] in
    Proofview.tclUNIT hint_lst
  end

(* Run a hint, using auto's strategy (for now)*)
let run_hint h = Hints.FullHint.run h Auto.hint_runner
