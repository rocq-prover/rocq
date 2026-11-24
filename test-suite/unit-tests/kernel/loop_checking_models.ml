open Utest
open Univ
open UnivConstraint

let log_out_ch = open_log_out_ch __FILE__

(* With the invariant checks, each model inferred by the loop checker is checked to be a model of
   all the clauses, and check_leq is compared with brute force on small graphs *)
let () = CDebug.set_flags "loop-checking-invariants"

let n = 4
let dp = Names.DirPath.make [Names.Id.of_string "Test"]
let lv = Array.init n (fun i -> Level.make (UGlobal.make dp "" i))
let univ atoms =
  let u (i, k) = Universe.addn (Universe.make lv.(i)) k in
  List.fold_left (fun acc x -> Universe.sup acc (u x)) (u (List.hd atoms)) (List.tl atoms)

let graph csts =
  let g = UGraph.set_local UGraph.initial_universes in
  let g = Array.fold_left (fun g l -> UGraph.add_universe l ~strict:false ~rigid:false g) g lv in
  fst (UGraph.merge_constraints
         (UnivConstraints.of_list (List.map (fun (l, r) -> (univ l, Le, univ r)) csts)) g)

(* The clauses 3 <= 1 and 3 <= max(1, 0) both update 3 when 1 is raised: the second one must see
   the value set by the first one *)
let same_conclusion () =
  ignore (graph [ ([3,0], [1,0; 0,0]); ([2,0], [2,1]); ([1,0], [2,0; 3,0]);
                  ([2,0], [0,0; 3,1; 1,1]); ([3,0], [1,0]) ]);
  true

(* [max(l) <= max(r)] in a valuation *)
let holds v (l, r) =
  let eval atoms = List.fold_left (fun acc (i, k) -> max acc (v.(i) + k)) min_int atoms in
  eval l <= eval r

(* Countermodels of these small graphs have values below [bound] *)
let bound = 7

let brute csts (x, q) =
  let v = Array.make n 0 in
  let rec go i =
    if i = n then not (List.for_all (holds v) csts) || holds v ([x], q)
    else
      let rec values a = a > bound || (v.(i) <- a; go (i + 1) && values (a + 1)) in
      values 0
  in
  go 0

let random () =
  Random.init 0;
  let atom () = (Random.int n, if Random.int 3 = 0 then 1 else 0) in
  let atoms () = List.init (1 + Random.int 3) (fun _ -> atom ()) in
  let bad = ref 0 in
  for _ = 1 to 3000 do
    let csts = List.init (2 + Random.int 5) (fun _ -> ([atom ()], atoms ())) in
    match graph csts with
    | exception UGraph.UniverseInconsistency _ -> ()
    | g ->
      let x = atom () and q = atoms () in
      if UGraph.check_leq g (univ [x]) (univ q) <> brute csts (x, q) then incr bad
  done;
  if !bad > 0 then Printf.fprintf log_out_ch "%d queries differ from brute force\n" !bad;
  Int.equal !bad 0

let tests = [
  mk_bool_test "same-conclusion" "a clause sees the value set by another one of the same conclusion"
    (same_conclusion ());
  mk_bool_test "random" "check_leq agrees with brute force on random small graphs" (random ());
]

let _ = run_tests __FILE__ log_out_ch tests
