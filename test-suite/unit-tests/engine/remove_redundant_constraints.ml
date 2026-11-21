open Utest
open Univ
open UnivConstraint

let log_out_ch = open_log_out_ch __FILE__

(* UState.remove_redundant_constraints must keep constraints with the same models: each
   constraint of the input must be entailed by the result *)

let dp = Names.DirPath.make [Names.Id.of_string "Test"]
let lv = Array.init 6 (fun i -> Level.make (UGlobal.make dp "" i))
let u ?(k = 0) i = Universe.addn (Universe.make lv.(i)) k
let umax l = List.fold_left (fun acc x -> Universe.sup acc x) (List.hd l) (List.tl l)

let graph csts =
  let g = UGraph.set_local UGraph.initial_universes in
  let g = Array.fold_left (fun g l -> UGraph.add_universe l ~strict:false ~rigid:false g) g lv in
  fst (UGraph.merge_constraints csts g)

let lost csts =
  let kept = UState.remove_redundant_constraints csts in
  let g = graph kept in
  UnivConstraints.filter (fun c -> not (UGraph.check_constraint g c)) csts

let pr csts = Pp.string_of_ppcmds (UnivConstraints.pr Level.raw_pr csts)

let keeps name csts =
  let csts = UnivConstraints.of_list csts in
  mk_bool_test name ("remove_redundant_constraints keeps the models of " ^ pr csts)
    (UnivConstraints.is_empty (lost csts))

(* [3 <= max(0, 1)] is [3 <= 1] because of [0 < max(0, 1+1)], i.e. [0 <= 1], which it then
   entails with [0 <= 3] *)
let premises = keeps "redundant-premises" [
    (u 0, Le, u 3);
    (u 3, Le, umax [u 0; u 1]);
    (u 0 ~k:1, Le, umax [u 0; u 1 ~k:1]) ]

(* [max(0, 2) <= 1] and [1 <= 0] make [0 = 1], then [max(0, 2) <= 1] is [2 <= 0], entailed by
   [2 <= 3 <= 0] *)
let merged = keeps "merged-universes" [
    (umax [u 0; u 2], Le, u 1);
    (u 1, Le, u 0);
    (u 2, Le, u 3);
    (u 3, Le, u 0) ]

(* [0 = 1] comes from the equality search: [0 <= max(1, 2)], [2 <= max(1, 4)], [4 <= 1] give
   [0 <= 1], so [1 = 0] with [1 <= 0]; then [0 <= max(1, 2)] is trivial *)
let entailed_merge = keeps "entailed-merge" [
    (u 0, Le, umax [u 1; u 2]);
    (u 1, Le, u 0);
    (u 2, Le, umax [u 1; u 4]);
    (u 4, Le, u 1);
    (u 2, Le, u 0) ]

(* Random constraint lists over a few universes *)
let random () =
  Random.init 42;
  let atom n = u (Random.int n) ~k:(if Random.int 3 = 0 then 1 else 0) in
  let rec umaxn n m = if m <= 1 then atom n else Universe.sup (atom n) (umaxn n (m - 1)) in
  let bad = ref [] in
  for _ = 1 to 20000 do
    let n = 3 + Random.int 3 in
    let csts = UnivConstraints.of_list (List.init (2 + Random.int 5) (fun _ ->
        let l = if Random.int 4 = 0 then umaxn n 2 else atom n in
        (l, (if Random.int 8 = 0 then Eq else Le), umaxn n (1 + Random.int 3)))) in
    match graph csts with
    | exception UGraph.UniverseInconsistency _ -> ()
    | _ -> if not (UnivConstraints.is_empty (lost csts)) then bad := csts :: !bad
  done;
  match !bad with
  | [] -> true
  | csts :: _ ->
    Printf.fprintf log_out_ch "%d lists lose constraints, e.g.\n%s\n" (List.length !bad) (pr csts);
    false

let random = mk_bool_test "random" "remove_redundant_constraints keeps the models of random lists"
    (random ())

let tests = [ premises; merged; entailed_merge; random ]

let _ = run_tests __FILE__ log_out_ch tests
