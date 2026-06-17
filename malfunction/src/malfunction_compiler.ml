open Lambda
open Asttypes

open Malfunction
open Malfunction_parser
open Malfunction_compat

(* List.map, but guarantees left-to-right evaluation *)
let rec lrmap f = function
| [] -> []
| (x :: xs) -> let r = f x in r :: lrmap f xs

let lprim p args = Lprim (p, args, loc_none)
let lbind n exp body =
  let id = fresh n in
  Llet (Strict, Pgenval, id, exp, body (Lvar id))

(* Enforce left-to-right evaluation order by introducing 'let' bindings *)

let rec reorder = function
| Mvar _
| Mnum _
| Mstring _
| Mglobal _ as t -> `Pure, t

| Mlambda (params, body) ->
  `Pure, Mlambda (params, snd (reorder body))

| Mapply (f, xs) ->
   reorder_sub `Impure (fun ev ->
     let f = ev f in
     let xs = lrmap ev xs in
     Mapply (f, xs))

| Mlet (bindings, body) ->
   let bindings = reorder_bindings bindings in
   let _, body = reorder body in
   `Impure, Mlet (bindings, body)

| Mswitch (e, cases) ->
   `Impure, Mswitch (snd (reorder e), List.map (fun (c, e) -> c, snd (reorder e)) cases)

| Mnumop1(op, ty, t) ->
   reorder_sub `Pure (fun ev ->
     Mnumop1(op, ty, ev t))

| Mnumop2(op, ty, t1, t2) ->
   reorder_sub `Pure (fun ev ->
     let t1 = ev t1 in
     let t2 = ev t2 in
     Mnumop2(op, ty, t1, t2))

| Mconvert(src, dst, t) -> 
   reorder_sub `Pure (fun ev ->
     Mconvert(src, dst, ev t))

| Mvecnew(ty, len, def) ->
   reorder_sub `Pure (fun ev ->
     let len = ev len in
     let def = ev def in
     Mvecnew(ty, len, def))

| Mvecget(ty, vec, idx) ->
   reorder_sub `Impure (fun ev ->
     let vec = ev vec in
     let idx = ev idx in
     Mvecget(ty, vec, idx))

| Mvecset(ty, vec, idx, v) ->
   reorder_sub `Impure (fun ev ->
     let vec = ev vec in
     let idx = ev idx in
     let v = ev v in
     Mvecset(ty, vec, idx, v))

| Mveclen(ty, vec) ->
   reorder_sub `Pure (fun ev ->
     let vec = ev vec in
     Mveclen(ty, vec))

| Mblock (n, ts) ->
   reorder_sub `Pure (fun ev ->
     Mblock(n, lrmap ev ts))

| Mfield (n, t) ->
   reorder_sub `Impure (fun ev ->
     Mfield (n, ev t))

| Mlazy e ->
  `Pure, Mlazy (snd (reorder e))

| Mforce e ->
   reorder_sub `Impure (fun ev ->
     Mforce (ev e))

and reorder_bindings bindings =
  bindings
  |> lrmap (function
    | `Unnamed t -> `Unnamed (snd (reorder t))
    | `Named (v, t) -> `Named (v, snd (reorder t))
    | `Recursive _ as ts -> ts (* must be functions *))

and reorder_sub p f =
  let bindings = ref [] in
  let r = f (fun e ->
    match reorder e with
    | `Pure, e -> e
    | `Impure, e ->
       let id = fresh "tmp" in
       bindings := (`Named (id, e)) :: !bindings;
       Mvar id) in
  match List.rev !bindings with
  | [] -> p, r
  | bindings -> `Impure, (Mlet (bindings, r))

module IntSwitch = struct

  (* Convert a list of possibly-overlapping intervals to a list of disjoint intervals *)

  type action = int (* lower numbers more important *)

  (* cases is a sorted list
     cases that begin lower appear first
     when two cases begin together, more important appears first *)

  type case = int * int * action (* start position, end position, priority *)
  type cases = case list (* sorted by start position then priority *)

  (* the inactive list is a list of (endpoint, priority) pairs representing
     intervals that we are currently inside, but are overridden by a more important one.
     subsequent elements of the list have strictly higher priorities and strictly later endpoints *)
  type inactive = (int * action) list

  let rec insert_inactive max act = function
    | [] -> [(max, act)]
    | (max', act') as i' :: rest when act' < act ->
       (* this interval should appear before the new one *)
       i' ::
         (if max' <= max then
             (* new interval will never be active *)
             rest
          else
             insert_inactive max act rest)

    | (max', act') :: rest when max' <= max ->
       assert (act < act');
       (* this interval will is contained by the new one, so never becomes active *)
       insert_inactive max act rest

    | ov ->
       (* new interval both more important and ends sooner, so prepend *)
       (max, act) :: ov

  type state =
    | Hole (* not currently in any interval *)
    | Interval of (* in an interval... *)
      int (* since this position *)
      * int (* until here *)
      * action (* with this action *)
      * inactive (* overriding these inactive intervals *)

  let state_suc = function
    | Hole -> failwith "state_suc of Hole undefined"
    | Interval (_, _, _, []) -> Hole
    | Interval (_, s_max, _, (max', act') :: rest) ->
       assert (s_max < max');
       (* can compute s_max + 1 without overflow, because inactive interval ends later *)
       Interval (s_max + 1, max', act', rest)

  type result = case list (* may have duplicate actions, disjoint, sorted by position *)
  let rec to_disjoint_intervals c_state (c_cases : cases) : result =
    match c_state, c_cases with
    | Hole, [] -> []

    | Hole, ((min, max, act) :: cases) ->
       to_disjoint_intervals (Interval (min, max, act, [])) cases

    | Interval (entered, max, act, _) as state, [] ->
       (entered, max, act) :: to_disjoint_intervals (state_suc state) []

    | Interval (s_entered, s_max, s_act, _) as state,
      (((min, _max, _act) :: _) as cases) when s_max < min ->
       (* active interval ends before this case begins *)
       (s_entered, s_max, s_act) :: to_disjoint_intervals (state_suc state) cases

    (* below here, we can assume min <= i.s_max: active interval overlaps current case *)
    | Interval (s_entered, s_max, s_act, s_inactive), ((_min, max, act) :: cases) when s_act < act ->
       (* no change to active interval, but this case may become an inactive one *)
       to_disjoint_intervals (Interval (s_entered, s_max, s_act, insert_inactive max act s_inactive)) cases

    | Interval (s_entered, s_max, s_act, s_inactive), ((min, max, act) :: cases) ->
       (* new active interval, so old one becomes inactive *)
       assert (s_entered <= min); assert (min <= s_max); assert (act < s_act);
       let r =
         if s_entered = min then
           (* old interval was not active long enough to produce output *)
           []
         else
           [(s_entered, min - 1, s_act)] in
       r @ to_disjoint_intervals
         (Interval (min, max, act, insert_inactive s_max s_act s_inactive)) cases


  (* unfortunately, this is not exposed from matching.ml, so copy-paste *)
  module Switcher = Switch.Make (struct
    type primitive = Lambda.primitive
    type loc = Location.t
    let _unused : loc option = None

    let eqint = Pintcomp Ceq
    let neint = Pintcomp Cne
    let leint = Pintcomp Cle
    let ltint = Pintcomp Clt
    let geint = Pintcomp Cge
    let gtint = Pintcomp Cgt

    type arg = Lambda.lambda
    type test = Lambda.lambda
    type act = Lambda.lambda

    let make_is_nonzero arg =
      (* https://github.com/ocaml/ocaml/pull/10681 *)
      Lprim (Pintcomp Cne,
             [arg; Lconst (Const_base (Const_int 0))],
             loc_none)

    let arg_as_test (arg : arg) : test = arg

    (* these are unused on some OCaml versions *)
    let _ = make_is_nonzero, arg_as_test

    let make_prim p args = lprim p args
    let make_offset arg n = match n with
    | 0 -> arg
    | _ -> lprim (Poffsetint n) [arg]

    let bind arg body =
      let newvar,newarg = match arg with
      | Lvar v -> v,arg
      | _      ->
          let newvar = fresh "switcher" in
          newvar,Lvar newvar in
      bind Alias newvar arg (body newarg)
    let make_const i = Lconst (Const_base (Const_int i))
    let make_isout h arg = lprim Pisout [h ; arg]
    let make_isin h arg = lprim Pnot [make_isout h arg]
    let make_if cond ifso ifnot = Lifthenelse (cond, ifso, ifnot)
    let make_switch arg cases acts =
      let l = ref [] in
      for i = Array.length cases-1 downto 0 do
        l := (i,acts.(cases.(i))) ::  !l
      done ;
      lswitch arg
        {sw_numconsts = Array.length cases ; sw_consts = !l ;
         sw_numblocks = 0 ; sw_blocks =  []  ;
         sw_failaction = None}
    let make_switch _loc = make_switch
    let make_catch d =
      match d with
      | Lstaticraise (i, []) -> i, (fun e -> e)
      | _ ->
         let i = next_raise_count () in
         i, fun e -> Lstaticcatch(e, (i, []), d)
    let make_exit i = Lstaticraise (i,[])
  end)

  let compile_int_switch scr overlapped_cases =
    assert (overlapped_cases <> []);
    let actions = Array.of_list (overlapped_cases |> List.map snd) in
    let cases = overlapped_cases
      |> List.mapi (fun idx (`Intrange (min, max), _) -> (min, max, idx))
      |> List.stable_sort (fun (min, _max, _idx) (min', _max', _idx') -> compare min min')
      |> to_disjoint_intervals Hole in
    let occurrences = Array.make (Array.length actions) 0 in
    let rec count_occurrences = function
      | [] -> assert false
      | [(_min, _max, act)] ->
         occurrences.(act) <- occurrences.(act) + 1
      | (_min, max, act) :: (((min', _max', _act') :: _) as rest) ->
         occurrences.(act) <- occurrences.(act) + 1;
         begin if max + 1 <> min' then
           (* When the interval list contains a hole, jump tables generated by
              switch.ml may contain spurious references to action 0.
              See PR#6805 *)
           occurrences.(0) <- occurrences.(0) + 1
         end;
         count_occurrences rest in
    count_occurrences cases;
    let open Switch in
    let store (*: Lambda.lambda t_store*) =
      { act_get = (fun () ->
          Array.copy actions);
        act_get_shared = (fun () ->
          actions |> Array.mapi (fun i act ->
            if occurrences.(i) > 1 then Shared act else Single act));
        act_store = (fun _ -> failwith "store unimplemented");
        act_store_shared = (fun _ -> failwith "store_shared unimplemented") } in
    let cases = Array.of_list cases in
    let (low, _, _) = cases.(0) and (_, high, _) = cases.(Array.length cases - 1) in
    Switcher.zyva Location.none (low, high) scr cases store
end

type global_value =
  | Glob_val of lambda
  | Glob_prim of Primitive.description
  | Identity

let lookup env v =
  let open Types in
  let open Primitive in
  let (path, descr) =
    try
      Env.lookup_value ~loc:Location.none (*parse_loc loc*) v env
    with Not_found ->
      let rec try_stdlib = let open Longident in function
        | Lident s -> Ldot (Lident "Stdlib", s)
        | Ldot (id, s) -> Ldot (try_stdlib id, s)
        | Lapply _ as l -> l in
      try Env.lookup_value ~loc:Location.none (try_stdlib v) env
      with Not_found ->
        failwith ("global not found: " ^ String.concat "." (Longident.flatten v)) in
  match descr.val_kind with
  | Val_reg -> Glob_val (transl_value_path loc_none env path)
  | Val_prim(p) ->
     (match p.prim_name with
     | "%equal" ->
        Glob_prim (Primitive.simple ~name:"caml_equal" ~arity:2 ~alloc:true)
     | "%compare" ->
        Glob_prim (Primitive.simple ~name:"caml_compare" ~arity:2 ~alloc:true)
     | "%identity" ->
        Identity
     | s when s.[0] = '%' ->
        failwith ("unimplemented primitive " ^ p.prim_name);
     | _ ->
        Glob_prim p)
  | _ -> failwith "unexpected kind of value"


let identity_to_lambda args =
  match args with
  | [] ->
     let param = fresh "prim" in
     lfunction [param] (Lvar param)
  | [x] -> x
  | fn :: args -> lapply fn args

let builtin env path args =
  let p = match path with
    | path1 :: pathrest ->
       List.fold_left (fun id s -> Longident.Ldot (id, s))
         (Longident.Lident path1) pathrest
    | _ -> assert false in
  match lookup env p with
  | Glob_val v ->
     lapply v args
  | Glob_prim p ->
     assert (p.prim_arity = List.length args);
     lprim (Pccall p) args
  | Identity ->
     identity_to_lambda args


let global_to_lambda = function
  | Glob_val v -> v
  | Glob_prim p ->
     (* Eta-expand this primitive. See translprim.ml. *)
     let rec make_params n =
       if n <= 0 then []
       else fresh "prim" :: make_params (n-1) in
     let params = make_params p.prim_arity in
     let body = lprim (Pccall p) (List.map (fun x -> Lvar x) params) in
     lfunction params body
  | Identity -> identity_to_lambda []

let rec to_lambda env = function
  | Mvar v ->
     Lvar v
  | Mlambda (params, e) ->
     if List.length params > max_arity () then
        (* we have to split the function *)
        let rec extractk k xs = match k, xs with
         | 0, xs -> [], xs
         | _, [] -> failwith "extractk"
         | k, x::xs ->
            let first, last = extractk (k-1) xs in
            x::first, last in
        let params1, params2 = extractk (max_arity ()) params in
        let e = Mlambda (params2, e) in
        lfunction params1 (to_lambda env e)
     else
        lfunction params (to_lambda env e)
  | Mapply (fn, args) ->
     let ap_func fn = lapply fn (List.map (to_lambda env) args) in
     (match fn with
     | Mglobal v ->
        (match lookup env v with
        | Glob_prim p when p.prim_arity = List.length args ->
           lprim (Pccall p) (List.map (to_lambda env) args)
        | Identity -> identity_to_lambda (List.map (to_lambda env) args)
        | g -> ap_func (global_to_lambda g))
     | fn ->
        ap_func (to_lambda env fn))
  | Mlet (bindings, body) ->
     bindings_to_lambda env bindings (to_lambda env body)
  | Mnum (`Int n) ->
     Lconst (Const_base (Const_int n))
  | Mnum (`Int32 n) ->
     Lconst (Const_base (Const_int32 n))
  | Mnum (`Int64 n) ->
     Lconst (Const_base (Const_int64 n))
  | Mnum (`Bigint n) ->
     (match Z.to_int n with
     | n' ->
        assert (Obj.repr n = Obj.repr n');
        Lconst (Const_base (Const_int n'))
     | exception Z.Overflow ->
        builtin env ["Z"; "of_string"] [Lconst (Const_immstring (Z.to_string n))])
  | Mnum (`Float64 f) ->
     Lconst (Const_base (Const_float (string_of_float f)))
  | Mstring s ->
     Lconst (Const_immstring s)
  | Mglobal v ->
     global_to_lambda (lookup env v)
  | Mswitch (scr, cases) ->
     let scr = to_lambda env scr in
     let rec flatten acc = function
       | ([], _) :: _ -> assert false
       | ([sel], e) :: rest -> flatten ((sel, to_lambda env e) :: acc) rest
       | (sels, e) :: rest ->
          let i = next_raise_count () in
          let cases = List.map (fun s -> s, Lstaticraise(i, [])) sels in
          Lstaticcatch (flatten (cases @ acc) rest, (i, []), to_lambda env e)
       | [] ->
          let rec partition (ints, tags, deftag) = function
            | [] -> (List.rev ints, List.rev tags, deftag)
            | (`Tag _, _) as c :: cases -> partition (ints, c :: tags, deftag) cases
            | (`Deftag, _) as c :: cases -> partition (ints, tags, Some c) cases
            | (`Intrange _, _) as c :: cases -> partition (c :: ints, tags, deftag) cases in
          let (intcases, tagcases, deftag) = partition ([],[],None) (List.rev acc) in
          lbind "switch" scr (fun scr ->
            let tagswitch = match tagcases, deftag with
              | [], None -> None
              | [_,e], None | [], Some (_, e) -> Some e
              | tags, def ->
                 let numtags = match def with
                   | Some _ -> (max_tag :> int)
                   | None -> 1 + List.fold_left (fun s (`Tag i, _) -> max s (i :> int)) (-1) tags in
                 Some (lswitch scr {
                   sw_numconsts = 0; sw_consts = []; sw_numblocks = numtags;
                   sw_blocks = List.map (fun (`Tag i, e) -> i, e) tags;
                   sw_failaction = match def with None -> None | Some (`Deftag,e) -> Some e
                 }) in
            let intswitch = match intcases with
              | [] -> None
              | [_,e] -> Some e
              | ints -> Some (IntSwitch.compile_int_switch scr ints) in
            match intswitch, tagswitch with
            | None, None -> assert false
            | None, Some e | Some e, None -> e
            | Some eint, Some etag ->
               Lifthenelse (lprim Pisint [scr], eint, etag)) in
     flatten [] cases
  | Mnumop1 (op, ty, e) ->
     let e = to_lambda env e in
     let ones32 = Const_base (Asttypes.Const_int32 (Int32.of_int (-1))) in
     let ones64 = Const_base (Asttypes.Const_int64 (Int64.of_int (-1))) in
     let code = match op, ty with
       | `Neg, `Int -> lprim Pnegint [e]
       | `Neg, `Int32 -> lprim (Pnegbint Pint32) [e]
       | `Neg, `Int64 -> lprim (Pnegbint Pint64) [e]
       | `Neg, `Bigint -> builtin env ["Z"; "neg"] [e]
       | `Neg, `Float64 -> lprim Pnegfloat [e]
       | `Not, `Int -> lprim Pnot [e]
       | `Not, `Int32 ->
          lprim (Pxorbint Pint32) [e; Lconst ones32]
       | `Not, `Int64 ->
          lprim (Pxorbint Pint64) [e; Lconst ones64]
       | `Not, `Bigint -> builtin env ["Z"; "lognot"] [e] 
       | `Not, `Float64 -> assert false in
     code
  | Mnumop2 (op, ((`Int|`Int32|`Int64) as ty), e1, e2) ->
     let e1 = to_lambda env e1 in
     let e2 = to_lambda env e2 in
     let prim = match ty with
       | `Int ->
          (match op with
            `Add -> Paddint | `Sub -> Psubint | `Mul -> Pmulint
          | `Div -> Pdivint Safe | `Mod -> Pmodint Safe
          | `And -> Pandint | `Or -> Porint | `Xor -> Pxorint
          | `Lsl -> Plslint | `Lsr -> Plsrint | `Asr -> Pasrint
          | `Lt -> Pintcomp Clt | `Gt -> Pintcomp Cgt
          | `Lte -> Pintcomp Cle | `Gte -> Pintcomp Cge
          | `Eq -> Pintcomp Ceq)
       | (`Int32 | `Int64) as ty ->
          let t = match ty with `Int32 -> Pint32  | `Int64 -> Pint64 in
          (match op with
            `Add -> Paddbint t | `Sub -> Psubbint t | `Mul -> Pmulbint t
          | `Div -> Pdivbint { size = t; is_safe = Safe }
          | `Mod -> Pmodbint { size = t; is_safe = Safe }
          | `And -> Pandbint t | `Or -> Porbint t | `Xor -> Pxorbint t
          | `Lsl -> Plslbint t | `Lsr -> Plsrbint t | `Asr -> Pasrbint t
          | `Lt -> Pbintcomp (t, Clt) | `Gt -> Pbintcomp (t, Cgt)
          | `Lte -> Pbintcomp (t, Cle) | `Gte -> Pbintcomp (t, Cge)
          | `Eq -> Pbintcomp (t, Ceq)) in
     lprim prim [e1; e2]
  | Mnumop2 (op, `Bigint, e1, e2) ->
     let e1 = to_lambda env e1 in
     let e2 = to_lambda env e2 in
     let fn = match op with
       | `Add -> "add" | `Sub -> "sub"
       | `Mul -> "mul" | `Div -> "div" | `Mod -> "rem"
       | `And -> "logand" | `Or -> "logor" | `Xor -> "logxor"
       | `Lsl -> "shift_left" | `Lsr -> "shift_right" | `Asr -> "shift_right"
       | `Lt -> "lt" | `Gt -> "gt"
       | `Lte -> "leq" | `Gte -> "geq" | `Eq -> "equal" in
     builtin env ["Z"; fn] [e1; e2]
  | Mnumop2 (op, `Float64, e1, e2) ->
     let e1 = to_lambda env e1 in
     let e2 = to_lambda env e2 in
     begin match op with
     | #binary_bitwise_op -> assert false
     | `Add -> lprim Paddfloat [e1; e2]
     | `Sub -> lprim Psubfloat [e1; e2]
     | `Mul -> lprim Pmulfloat [e1; e2]
     | `Div -> lprim Pdivfloat [e1; e2]
     | `Mod -> builtin env ["Stdlib"; "mod_float"] [e1; e2]
     | #binary_comparison as op ->
        let cmp_to_float_comparison op = 
          match op with
          | `Lt -> CFlt
          | `Gt -> CFgt
          | `Lte -> CFle
          | `Gte -> CFge
          | `Eq -> CFeq
        in
        let cmp = cmp_to_float_comparison op in
        lprim (Pfloatcomp cmp) [e1; e2]
     end
  | Mconvert (src, dst, e) ->
     let e = to_lambda env e in
     begin match src, dst with
       | `Bigint, `Bigint
       | `Int, `Int
       | `Int32, `Int32
       | `Int64, `Int64
       | `Float64, `Float64 -> e
       | `Bigint, ((`Int|`Int32|`Int64) as dst) ->
          (* Zarith raises exceptions on overflow, but we truncate conversions. Not fast. *)
          let width = match dst with 
            | `Int -> Sys.word_size - 1
            | `Int32 -> 32
            | `Int64 -> 64 in
          let range = Z.(shift_left (of_int 1) width) in
          let truncated =
            lbind "range"
             (builtin env ["Z"; "of_string"] [Lconst (Const_immstring (Z.to_string range))])
             (fun range ->
               lbind "masked"
                 (builtin env ["Z"; "logand"] [e;
                      builtin env ["Z"; "sub"] [range;
                                                Lconst (Const_base (Const_int 1))]])
                 (fun masked ->
                   Lifthenelse (builtin env ["Z"; "testbit"] 
                                  [masked; Lconst (Const_base (Const_int (width - 1)))],
                                builtin env ["Z"; "sub"] [masked; range],
                                masked))) in
          let fn = match dst with
            | `Int -> "to_int"
            | `Int32 -> "to_int32"
            | `Int64 -> "to_int64" in
          builtin env ["Z"; fn] [truncated]
       | ((`Int|`Int32|`Int64) as src), `Bigint ->
          let fn = match src with
            | `Int -> "of_int"
            | `Int32 -> "of_int32"
            | `Int64 -> "of_int64" in
          builtin env ["Z"; fn] [e]
       | `Int, `Int32 ->
          lprim (Pbintofint Pint32) [e]
       | `Int, `Int64 ->
          lprim (Pbintofint Pint64) [e]
       | `Int32, `Int ->
          lprim (Pintofbint Pint32) [e]
       | `Int64, `Int ->
          lprim (Pintofbint Pint64) [e]
       | `Int32, `Int64 ->
          lprim (Pcvtbint(Pint32, Pint64)) [e]
       | `Int64, `Int32 ->
          lprim (Pcvtbint(Pint64, Pint32)) [e]
       | `Int, `Float64 ->
          lprim Pfloatofint [e]
       | `Int32, `Float64 ->
          builtin env ["Int32"; "to_float"] [e]
       | `Int64, `Float64 ->
          builtin env ["Int64"; "to_float"] [e]
       | `Bigint, `Float64 ->
          builtin env ["Z"; "to_float"] [e]
       (* FIXME: error handling on overflow *)
       | `Float64, `Int ->
          lprim Pintoffloat [e]
       | `Float64, `Int32 ->
          builtin env ["Int32"; "of_float"] [e]
       | `Float64, `Int64 ->
          builtin env ["Int64"; "of_float"] [e]
       | `Float64, `Bigint ->
          builtin env ["Z"; "of_float"] [e]
     end
  | Mvecnew (`Array, len, def) ->
     builtin env ["Array"; "make"] [to_lambda env len; to_lambda env def]
  | Mvecnew (`Bytevec, len, def) ->
     builtin env ["String"; "make"] [to_lambda env len; to_lambda env def]
  | Mvecget (ty, vec, idx) ->
     let prim = match ty with
       | `Array -> Parrayrefs Paddrarray
       | `Bytevec -> Pbytesrefs
(*       | `Floatvec -> Parrayrefs Pfloatarray *) in
     lprim prim [to_lambda env vec; to_lambda env idx]
  | Mvecset (ty, vec, idx, v) ->
     let prim = match ty with
       | `Array -> Parraysets Paddrarray
       | `Bytevec -> Pbytessets
(*       | `Floatvec -> Parraysets Pfloatarray *) in
     lprim prim [to_lambda env vec; to_lambda env idx; to_lambda env v]
  | Mveclen (ty, vec) ->
     let prim = match ty with
       | `Array -> Parraylength Paddrarray
       | `Bytevec -> Pbyteslength
(*       | `Floatvec -> Parraylength Pfloatarray *) in
     lprim prim [to_lambda env vec]
  | Mblock (tag, vals) ->
     lprim (Pmakeblock (tag, Immutable, None)) (List.map (to_lambda env) vals)
  | Mfield (idx, e) ->
      lprim (pfield idx) [to_lambda env e]
  | Mlazy e ->
     let fn = lfunction [fresh "param"] (to_lambda env e) in
     lprim (Pmakeblock (Config.lazy_tag, Mutable, None)) [fn]
  | Mforce e ->
     Matching.inline_lazy_force (to_lambda env e) loc_none

and bindings_to_lambda env bindings body =
  List.fold_right (fun b rest -> match b with
  | `Unnamed e ->
     Lsequence (to_lambda env e, rest)
  | `Named (n, e) ->
     Llet (Strict, Pgenval, n, to_lambda env e, rest)
  | `Recursive bs ->
     lletrec (List.map (fun (n, e) -> (n, to_lambda env e)) bs) rest)
    bindings body

let setup_options options =
  Clflags.native_code := true;
  Clflags.flambda_invariant_checks := true;
  Clflags.nopervasives := false;
  Clflags.dump_lambda := false;
  Clflags.dump_cmm := false;
  Clflags.keep_asm_file := false;
  Clflags.include_dirs := [Findlib.package_directory "zarith"];
  Clflags.inlining_report := false;
  Clflags.dlcode := true;
  Clflags.shared := false;
  Clflags.(default_simplify_rounds := 0);
  (* FIXME: should we use classic_arguments for non-flambda builds? *)


  (* Hack: disable the "no cmx" warning for zarith *)
  let _ = Warnings.parse_options false "-58" in
  assert (not (Warnings.is_active (Warnings.No_cmx_file "asdf")));

  (options |> List.iter @@ function
  | `Verbose ->
     Clflags.dump_lambda := true;
     Clflags.dump_cmm := true;
     Clflags.keep_asm_file := true;
     Clflags.inlining_report := true
     (*
       If anyone wants to keep these, there should probably be another option for where to put them.
       (rather than leaving stale temporary directories around)
      *)
  | `Shared ->
     Clflags.shared := true
  | `Include dir ->
     Clflags.include_dirs := dir :: !Clflags.include_dirs
  | `Package s -> 
     let packages = String.split_on_char ',' s in
     let dirs = List.map Findlib.package_directory packages in
     Clflags.include_dirs := dirs @ !Clflags.include_dirs
  | `ForPack s -> Clflags.for_package := Some s
  | `Dontlink _ -> ()
  | `Linkpkg -> ()
  | `Debug -> Clflags.debug := true
  | `Rectypes -> Clflags.recursive_types := true
  | `Thread -> ()
  | `Optimize ->   Clflags.(
    default_simplify_rounds := 2;
    use_inlining_arguments_set o2_arguments;
    use_inlining_arguments_set ~round:0 o1_arguments);
  | `Bytecode -> Clflags.native_code := false
   );
  (* FIXME: should we use classic_arguments for non-flambda builds? *)

  Compenv.(readenv Format.std_formatter (Before_compile "malfunction"));
  compmisc_init_path ()

let module_to_lambda ?options ~module_name:_ ~module_id (Mmod (bindings, exports)) =
  setup_options (match options with Some o -> o | None -> []);
  let print_if flag printer arg =
    if !flag then Format.printf "%a@." printer arg;
    arg in

  let env = Compmisc.initial_env () in
  let module_size, code =
    let bindings = reorder_bindings bindings in
    let exports = List.map (fun e -> snd (reorder e)) exports in
    if Config.flambda || not !Clflags.native_code then
      List.length exports,
      bindings_to_lambda env bindings
        (lprim (Pmakeblock (0, Immutable, None)) (List.map (to_lambda env) exports))
    else begin
      let loc = loc_none (* FIXME *) in
      let num_exports = List.length exports in
      (* Compile all of the bindings, store at positions num_exports + i,
         then compile the exports. See Translmod.transl_store_gen. *)
      let module_length = ref (-1) in
      let mod_store pos e =
        Lprim (Psetfield (pos, Pointer, Root_initialization),
               [Lprim (Pgetglobal module_id, [], loc); e], loc) in
      let mod_load pos =
        Lprim (pfield pos,
               [Lprim (Pgetglobal module_id, [], loc)], loc) in
      let transl_exports subst =
        let exps = List.mapi (fun i e -> mod_store i (Subst.apply subst (to_lambda env e))) exports in
        List.fold_right (fun x xs -> Lsequence (x, xs)) exps (Lconst Lambda.const_unit) in
      let rec transl_toplevel_bindings pos subst = function
        | `Unnamed e :: rest ->
           Lsequence (Subst.apply subst (to_lambda env e),
                      transl_toplevel_bindings pos subst rest)
        | `Named (n, e) :: rest ->
           let lam =
             Llet (Strict, Pgenval, n, Subst.apply subst (to_lambda env e), mod_store pos (Lvar n)) in
           Lsequence (lam,
                      transl_toplevel_bindings
                        (pos + 1)
                        (Subst.add n (mod_load pos) subst)
                        rest)
        | `Recursive bs :: rest ->
           let ids = List.map fst bs in
           let stores = ids |> List.mapi (fun i n -> mod_store (pos + i) (Lvar n)) in
           let stores = List.fold_right (fun x xs -> Lsequence (x, xs))
                          stores (Lconst Lambda.const_unit) in
           let lam =
             lletrec (bs |> List.map (fun (n, e) ->
                                (n, Subst.apply subst (to_lambda env e))))
                      stores in
           let id_load = ids |> List.mapi (fun i n -> (n, mod_load (pos + i))) in
           let subst = List.fold_left (fun subst (n, l) -> Subst.add n l subst) subst id_load in
           Lsequence (lam, transl_toplevel_bindings (pos + List.length ids) subst rest)

        | [] -> module_length := pos; transl_exports subst in
      let r = transl_toplevel_bindings num_exports Subst.empty bindings in
      !module_length, r
    end in

  let lambda = code
  |> print_if Clflags.dump_rawlambda Printlambda.lambda
  |> simplify_lambda
  |> print_if Clflags.dump_lambda Printlambda.lambda in

  (module_size, lambda)



let backend = (module struct
  include Compilenv
  include Import_approx
  include Arch
  let max_sensible_number_of_arguments =
    Proc.max_arguments_for_tailcalls - 1
end : Backend_intf.S)

type outfiles =
  | Out_native of {cmxfile: string; rest: string list}
  | Out_bytecode of {cmofile: string; rest: string list}

let delete_temps outfiles =
  let temps =
    match outfiles with
    | Out_native {cmxfile; rest} -> cmxfile::rest
    | Out_bytecode {cmofile; rest} -> cmofile::rest
  in
  List.iter Misc.remove_file temps

type options = [`Verbose | `Shared | `ForPack of string | `Include of string | `Package of string | `Dontlink of string | `Linkpkg | `Debug | `Rectypes | `Thread | `Optimize | `Bytecode] list

let ensure_cmi ~module_name ~filename =
  let cmi = module_name ^ ".cmi" in
  Compilenv.reset ?packname:!Clflags.for_package module_name;
  match load_path_find_uncap cmi with
  | file -> env_read_signature ~module_name ~file, None
  | exception Not_found ->
     let chop_ext =
         Misc.chop_extensions
       in
     let mlifile = chop_ext filename ^ !Config.interface_suffix in
     if Sys.file_exists mlifile then
       Typemod.(raise(Error(Location.in_file filename,
                            Env.empty,
                            Interface_not_compiled cmi)))
     else
       (* hackily generate an empty cmi file *)
       let cmifile = String.uncapitalize_ascii cmi in
       let mlifile = String.uncapitalize_ascii (module_name ^ ".mli") in
       let ch = open_out mlifile in
       output_string ch "(* autogenerated mli for malfunction *)\n";
       close_out ch;
       ignore (Sys.command ("ocamlc -c " ^ mlifile));
       Misc.remove_file mlifile;
       if not (Sys.file_exists cmifile) then failwith "Failed to generate empty cmi file";
       env_read_signature ~module_name ~file:cmifile, Some cmifile


let lambda_to_cmx ~options ~filename ~prefixname ~module_name ~module_id lmod =
  let ppf = Format.std_formatter in
  let cmxfile = prefixname ^ ".cmx" in
  let objfile = prefixname ^ Config.ext_obj in
  let outfiles = ref [objfile] in
  setup_options options;
  try
    env_set_unit_name ~filename ~prefixname ~module_name;
    let _, cmifile = ensure_cmi ~module_name ~filename in
    outfiles := Option.to_list cmifile @ !outfiles;
    (* FIXME: may need to add modules referenced only by "external" to this.
       See Translmod.primitive_declarations and its use in Asmgen. *)
    (* FIXME: Translprim.get_used_primitives (see translmod.ml)? *)
    (* FIXME: Translmod.required_globals? Env.reset_required_globals? Should this be in to_lambda? *)
    let required_globals = Ident.Set.of_list (Env.get_required_globals ()) in
    compile_implementation ~prefixname ~filename ~module_id ~backend ~required_globals ~ppf lmod;
    Compilenv.save_unit_info cmxfile;
    Warnings.check_fatal ();
    Out_native {cmxfile; rest = !outfiles}
  with e ->
    let bt = Printexc.get_raw_backtrace () in
    delete_temps (Out_native {cmxfile; rest = !outfiles});
    Printexc.raise_with_backtrace e bt

let lambda_to_cmo ~options ~filename ~prefixname ~module_name ~module_id (_size, lambda) =
  let cmofile = prefixname ^ ".cmo" in
  let outfiles = ref [] in
  setup_options options;
  try
    env_set_unit_name ~filename ~prefixname ~module_name;
    let _, cmifile = ensure_cmi ~module_name ~filename in
    outfiles := Option.to_list cmifile @ !outfiles;
    (* FIXME: may need to add modules referenced only by "external" to this.
       See Translmod.primitive_declarations and its use in Asmgen. *)
    (* FIXME: Translprim.get_used_primitives (see translmod.ml)? *)
    (* FIXME: Translmod.required_globals? Env.reset_required_globals? Should this be in to_lambda? *)
    let lambda = lprim (Psetglobal module_id) [lambda] in
    let required_globals = Ident.Set.of_list (Env.get_required_globals ()) in
    let bytecode = Bytegen.compile_implementation module_name lambda in
    let oc = open_out_bin cmofile in
    Fun.protect ~finally:(fun () -> close_out oc) (fun () ->
      emit_bytecode_to_file oc module_name cmofile ~required_globals bytecode);
    Warnings.check_fatal ();
    Out_bytecode {cmofile; rest = !outfiles}
  with e ->
    delete_temps (Out_bytecode {cmofile; rest = !outfiles});
    raise e

let compile_module ?(options=[]) ~filename modl =
  (* FIXME: do we really want to go through Clflags here? See Compenv.output_prefix *)
  let prefixname = Compenv.output_prefix filename in
  let module_name =
    prefixname
    |> Filename.basename
    |> Filename.remove_extension
    |> String.capitalize_ascii in
  let lambda_to_output =
    if List.mem `Bytecode options
    then lambda_to_cmo
    else lambda_to_cmx
  in
  if not (is_unit_name module_name) then
    raise (Invalid_argument ("Invalid module name " ^ module_name));
  let module_id = Ident.create_persistent module_name in
  modl
  |> module_to_lambda ~module_name ~module_id ~options
  |> lambda_to_output ~options ~filename ~prefixname ~module_name ~module_id

let compile_file ~options filename =
  let lexbuf = Lexing.from_channel (open_in filename) in
  Lexing.(lexbuf.lex_curr_p <-
            { lexbuf.lex_curr_p with pos_fname = filename });
  let modl = Malfunction_parser.read_module lexbuf in
  compile_module ~options ~filename modl

let compile_cmx ?(options=[]) filename =
  compile_file ~options filename

let compile_cmo ?(options=[]) filename =
  compile_file ~options:(`Bytecode :: options) filename

(* copied from opttoploop.ml *)
external ndl_run_toplevel: string -> string -> (Obj.t, string) result
  = "caml_natdynlink_run_toplevel"
external ndl_loadsym: string -> Obj.t = "caml_natdynlink_loadsym"

let code_id = ref 0

let compile_and_load ?(options : options =[]) e =
  if not Dynlink.is_native then
    failwith "Loading malfunction values works only in native code";
  let tmpdir = Filename.temp_file "malfunction" ".tmp" in
  (* more than a little horrible *)
  Unix.unlink tmpdir;
  Unix.mkdir tmpdir 0o700;
  let old_cwd = Sys.getcwd () in
  Sys.chdir tmpdir;
  incr code_id;
  let modname = "Malfunction_Code_" ^ string_of_int (!code_id) in
  let modname_uncap = String.uncapitalize_ascii modname in
  let options = `Shared :: options in
  let tmpfiles = compile_module ~options ~filename:modname_uncap (Mmod ([], [e])) in
  let cmxfile =
    match tmpfiles with
    | Out_native o -> o.cmxfile
    | Out_bytecode _ -> failwith "Bytecode loading unsupported"
  in
  setup_options options;  (* rescan load path *)
  begin try
    Asmlink.link_shared ~ppf_dump:Format.err_formatter [cmxfile] (modname_uncap ^ ".cmxs")
  with
  | Asmlink.Error e ->
     let msg = Format.asprintf "Asmlink error: %a" Asmlink.report_error e in
     failwith msg
  end;
  let cmxs = tmpdir ^ Filename.dir_sep ^ modname_uncap ^ ".cmxs" in
  (match ndl_run_toplevel cmxs modname with
  | Ok _ -> ()
  | Error s -> failwith ("loading failed: " ^ s));
  let res = Obj.field (ndl_loadsym (Compilenv.symbol_for_global (Ident.create_persistent modname))) 0 in
  delete_temps tmpfiles;
  Misc.remove_file cmxs;
  Sys.chdir old_cwd;
  Unix.rmdir tmpdir;
  res



let link_executable ?(options=[]) output tmpfiles =
   let cmxfile =
     match tmpfiles with
     | Out_native o -> o.cmxfile
     | Out_bytecode _ -> failwith "Bytecode linking unsupported"
   in
   let pkgs =
      options |> (List.filter_map @@ 
      function
      | `Package s -> Some s
      | _ -> None)
   in
   let linkpkg = options |> (List.exists @@ (function `Linkpkg -> true | _ -> false)) in
   let dontlink =
      options |> (List.filter_map @@ 
      function
      | `Dontlink s -> Some s
      | _ -> None)
   in
   let thread =
      options |> (List.exists @@ 
      function
      | `Thread -> true
      | _ -> false)
   in
   let pkgs =
     match pkgs with
     | [] -> []
     | pkgs -> ["-package"; String.concat "," pkgs] in
   let dontlink = 
      if dontlink = [] then []
      else ["-dontlink"; String.concat "," dontlink]
   in
   let linkpkg = if linkpkg then ["-linkpkg"] else [] in
   let thread = if thread then ["-thread"] else [] in
   let opts = String.concat " " (thread @ linkpkg @ pkgs @ dontlink) in
   (* urgh *)
   Sys.command (Printf.sprintf "ocamlfind ocamlopt %s '%s' -o '%s'"
                 opts cmxfile output)
