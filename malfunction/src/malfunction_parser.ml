open Malfunction
open Malfunction_sexp

type moduleexp =
| Mmod of binding list * t list

(* Compiling from sexps *)

let fail loc fmt =
  let k _ppf =
    raise (SyntaxError (loc, Format.flush_str_formatter ())) in
  Format.kfprintf k Format.str_formatter ("@[" ^^ fmt ^^ "@]")

module StrMap = Map.Make (struct type t = string let compare = compare end)

let bind_local _loc locals s ident =
  StrMap.add s ident locals

let parse_arglist = function
  | loc, List [] ->
     fail loc "a nonempty argument list is required"
  | loc, List args ->
     let idents = args |> List.map (function
       | _loc, Var s ->
          s, fresh s
       | loc, _ -> fail loc "Expected a list of variables") in
     let env = List.fold_left (fun env (s, ident) ->
       if StrMap.mem s env then
         fail loc "Parameter %s bound multiple times" s
       else
         bind_local loc env s ident) StrMap.empty idents in
     List.map snd idents, env
  | loc, _ -> fail loc "Expected a list of atoms"

let parse_tag = function
| loc, List [_, Atom "tag"; _, Atom n] ->
   begin match int_of_string n with
   | n when 0 <= n && n < (max_tag :> int) -> n
   | n -> fail loc "tag %d out of range [0,%d]" n ((max_tag :> int)-1)
   | exception (Failure _) -> fail loc "invalid tag %s" n end
| loc, _ -> fail loc "invalid tag"

let inttypes = [`Int, ".int" ; `Int32, ".i32" ; `Int64, ".i64" ; `Bigint, ".ibig"]
let numtypes = inttypes @ [`Float64, ".f64"]

let (unary_intops_by_name : (unary_num_op * numtype) StrMap.t),
    (binary_intops_by_name : (binary_num_op * numtype) StrMap.t),
    (conversions_by_name : (numtype * numtype) StrMap.t),
    (numtypes_by_name : numtype StrMap.t) =
  let unary_ops = [ `Neg, "neg"; `Not, "not" ] in
  let binarith_ops = [ `Add, "+" ; `Sub, "-" ; `Mul, "*" ; `Div, "/" ; `Mod, "%" ] in
  let bitwise_ops = [ `And, "&" ; `Or, "|" ; `Xor, "^" ; `Lsl, "<<" ; `Lsr, ">>"  ; `Asr, "a>>" ] in
  let comparison_ops = [ `Lt, "<" ; `Gt, ">" ; `Lte, "<=" ; `Gte, ">=" ; `Eq, "==" ] in
  let binary_ops =
    binarith_ops @ bitwise_ops @ comparison_ops in
  let deftypes = (`Int, "") :: numtypes in
  let () = (* check that all cases are handled here *)
    List.iter (function #unary_num_op, _ -> () | _ -> assert false) unary_ops;
    List.iter (function #binary_num_op, _ -> () | _ -> assert false) binary_ops;
    List.iter (function #numtype, _ -> () | _ -> assert false) numtypes in
  List.fold_right (fun (ty,tyname) ->
    List.fold_right (fun (op,opname) ->
      StrMap.add (opname ^ tyname) (op, ty)) unary_ops) deftypes StrMap.empty,
  (List.fold_right (fun (ty,tyname) ->
     List.fold_right (fun (op,opname) ->
       StrMap.add (opname ^ tyname) (op, ty)) binary_ops) deftypes StrMap.empty
   |> List.fold_right (fun (_ty,tyname) ->
        List.fold_right (fun (_op, opname) ->
          StrMap.remove (opname ^ tyname)) bitwise_ops) [`Float64, ".f64"]),
  List.fold_right (fun (op1, opname1) ->
    List.fold_right (fun (op2, opname2) ->
      StrMap.add ("convert" ^ opname1 ^ opname2) (op1, op2)) numtypes) numtypes StrMap.empty,
  List.fold_right (fun (ty, name) ->
      StrMap.add name ty) numtypes StrMap.empty


let vecops_by_name op =
  List.fold_right (fun (ty,tyname) ->
    StrMap.add (op ^ tyname) ty)
    [`Array, ""; `Bytevec, ".byte"]
    StrMap.empty
let vec_new_by_name = vecops_by_name "makevec"
let vec_get_by_name = vecops_by_name "load"
let vec_set_by_name = vecops_by_name "store"
let vec_len_by_name = vecops_by_name "length"

(*
(let
  (a 42)
  (b 17)
  (_ 421)
  (rec (a (lambda)))

*)

let rec parse_bindings loc env acc = function
  | [e] ->
     List.rev acc, env, e
  | (loc, List [_, Atom "_"; e]) :: bindings ->
     parse_bindings loc env (`Unnamed (parse_exp env e) :: acc) bindings
  | (loc, List [_, Var s; e]) :: bindings ->
     let ident = fresh s in
     let env' = bind_local loc env s ident in
     parse_bindings loc env' (`Named (ident, parse_exp env e) :: acc) bindings
  | (loc, List ((_, Atom "rec") :: recs)) :: bindings ->
     let recs = recs |> List.map (function
       | _, List [_, Var s; _, List ((_, Atom ("lambda"|"lazy")) :: _) as e] ->
          (s, fresh s, e)
       | _, List [_, Var _; _] ->
          fail loc "all members of a recursive binding must be functions or lazy"
       | loc, _ ->
          fail loc "expected recursive bindings") in
     let env' = List.fold_left (fun env (s, id, _) ->
       bind_local loc env s id) env recs in
     let recs = recs |> List.map (fun (_, id, e) ->
       (id, parse_exp env' e)) in
     parse_bindings loc env' (`Recursive recs :: acc) bindings
  | _ -> fail loc "no bindings?"

and parse_exp env (loc, sexp) = match sexp with
  | Var s when StrMap.mem s env ->
     Mvar (StrMap.find s env)

  | Var s ->
     fail loc "'%s' is unbound" s

  | List [_, Atom "lambda"; args; exp] ->
     let (params, newenv) = parse_arglist args in
     let env = StrMap.fold StrMap.add newenv env in
     Mlambda (params, parse_exp env exp)

  | List ((_loc, Atom "apply") :: func :: args) ->
     if args = [] then fail loc "Expected a nonempty parameter list";
     Mapply (parse_exp env func, List.map (parse_exp env) args)

  | List ((loc, Atom "let") :: bindings) ->
     let (bindings, env, e) = parse_bindings loc env [] bindings in
     Mlet (bindings, parse_exp env e)

  | List ((_loc, Atom "seq") :: ((_ :: _) as exps)) ->
     let rec to_let acc = function
       | [] -> assert false
       | [e] -> Mlet (List.rev acc, parse_exp env e)
       | e :: es -> to_let (`Unnamed (parse_exp env e) :: acc) es in
     to_let [] exps

  | List ((_, Atom "switch") :: exp :: cases) ->
     let parse_selector s = try match s with
       | _, List [_, Atom "tag"; _, Atom "_"] -> `Deftag
       | _, List ([_, Atom "tag"; _]) as t -> `Tag (parse_tag t)
       | _, List [_, Atom min; _, Atom max] -> `Intrange (int_of_string min, int_of_string max)
       | _, Atom "_" -> `Intrange (min_int, max_int)
       | _, Atom n -> `Intrange (int_of_string n, int_of_string n)
       | loc, _ -> fail loc "invalid selector"
       with Failure _ -> fail loc "invalid selector" in

     let rec parse_case loc acc = function
       | [s; e] -> List.rev (parse_selector s :: acc), parse_exp env e
       | (s :: c) -> parse_case loc (parse_selector s :: acc) c
       | _ -> fail loc "invalid case" in

     let cases = List.map (function
       | loc, List c -> parse_case loc [] c
       | loc, _ -> fail loc "invalid case") cases in

     if (List.length (List.sort_uniq compare cases) <> List.length cases) then
       fail loc "duplicate cases";

     Mswitch (parse_exp env exp, cases)

  | List [_, Atom "if"; cond; tt; ff] ->
     Mswitch (parse_exp env cond, 
              [[`Intrange (0, 0)], parse_exp env ff;
               [`Intrange (min_int, max_int); `Deftag], parse_exp env tt])

  | List [_, Atom s; e] when StrMap.mem s unary_intops_by_name ->
     let (op, ty) = StrMap.find s unary_intops_by_name in
     Mnumop1 (op, ty, parse_exp env e)

  | List [_, Atom s; e1; e2] when StrMap.mem s binary_intops_by_name ->
     let (op, ty) = StrMap.find s binary_intops_by_name in
     Mnumop2 (op, ty, parse_exp env e1, parse_exp env e2)

  | List [_, Atom s; e1] when StrMap.mem s conversions_by_name ->
     let (ty1, ty2) = StrMap.find s conversions_by_name in
     Mconvert (ty1, ty2, parse_exp env e1)

  | List [_, Atom op; len; def] when StrMap.mem op vec_new_by_name ->
     Mvecnew (StrMap.find op vec_new_by_name, parse_exp env len, parse_exp env def)

  | List [_, Atom op; vec; idx] when StrMap.mem op vec_get_by_name ->
     Mvecget (StrMap.find op vec_get_by_name, parse_exp env vec, parse_exp env idx)

  | List [_, Atom op; vec; idx; v] when StrMap.mem op vec_set_by_name ->
     Mvecset (StrMap.find op vec_set_by_name, parse_exp env vec, parse_exp env idx, parse_exp env v)

  | List [_, Atom op; vec] when StrMap.mem op vec_len_by_name ->
     Mveclen (StrMap.find op vec_len_by_name, parse_exp env vec)

  | List ((_, Atom "block") :: tag :: fields) ->
     Mblock (parse_tag tag, List.map (parse_exp env) fields)

  | List [_, Atom "field"; _, Atom n; e] ->
     let n = match int_of_string n with
       | n -> n
       | exception (Failure _) -> fail loc "invalid field number" in
     Mfield (n, parse_exp env e)

  | String s ->
     Mstring s

  | List [_, Atom "lazy"; e] ->
     Mlazy (parse_exp env e)

  | List [_, Atom "force"; e] ->
     Mforce (parse_exp env e)

  | List ((_, Atom "global") :: path) ->
     Mglobal (path
       |> (function
           | (l, Var "Pervasives")::p ->
              Printf.fprintf stderr "Warning: global $Pervasives is deprecated, use $Stdlib instead.\n";
              (l, Var "Stdlib")::p
           | p -> p)
       |> List.map (function
         | _, Var s -> s
         | _, _ -> fail loc "module path required")
       |> function
         | [] -> fail loc "empty global path"
         | path1 :: pathrest ->
            List.fold_left (fun id s ->
              Longident.Ldot (id, s)) (Longident.Lident path1) pathrest)

  | List ((_, Atom s) :: rest) ->
     fail loc "Unknown %d-ary operation %s" (List.length rest) s

  | Atom "nan" -> Mnum (`Float64 nan)
  | Atom "infinity" -> Mnum (`Float64 infinity)
  | Atom "neg_infinity" -> Mnum (`Float64 neg_infinity)

  | Atom s ->
     let orig = s in
     let s, ext = match String.rindex s '.' with
       | i ->
          String.sub s 0 i,
          String.sub s i (String.length s - i)
       | exception Not_found ->
          s, ".int" in
     begin
       try match StrMap.find ext numtypes_by_name with
       | `Int -> Mnum (`Int (int_of_string s))
       | `Int32 -> Mnum (`Int32 (Int32.of_string s))
       | `Int64 -> Mnum (`Int64 (Int64.of_string s))
       | `Bigint -> Mnum (`Bigint (Z.of_string s))
       | `Float64 -> Mnum (`Float64 (float_of_string s))
       with
       | Not_found ->
          (try Mnum (`Float64 (float_of_string orig))
           with Invalid_argument _ ->
             fail loc "unknown constant type: '%s'" ext)
       | Invalid_argument _ | Failure _ ->
          fail loc "constant '%s' out of bounds for '%s'" s ext
     end

  | _ -> fail loc "syntax error"


let parse_mod (loc, sexp) = match sexp with
  | List ((_, Atom "module") :: rest) ->
     let (bindings, env, exports) = parse_bindings loc StrMap.empty [] rest in
     let exports = match exports with
       | _, List ((_, Atom "export") :: exports) ->
          List.map (parse_exp env) exports
       | _ -> fail loc "export list?" in
     Mmod (bindings, exports)
  | _ -> fail loc "mod?"

let read_expression lexbuf =
  parse_exp StrMap.empty (Malfunction_sexp.read_next_sexp lexbuf)

let parse_expression t =
  parse_exp StrMap.empty t

let read_module lexbuf =
  parse_mod (Malfunction_sexp.read_only_sexp lexbuf)
