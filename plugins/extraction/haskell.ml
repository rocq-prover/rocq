(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(*s Production of Haskell syntax. *)

open Pp
open CErrors
open Util
open Names
open Table
open Miniml
open Mlutil
open Common

(*s Haskell renaming issues. *)
let pr_lower_id id = str (String.uncapitalize_ascii (Id.to_string id))
let pr_upper_id id = str (String.capitalize_ascii (Id.to_string id))

let keywords =
  List.fold_right (fun s -> Id.Set.add (Id.of_string s))
  [ "Any"; "case"; "class"; "data"; "default"; "deriving"; "do"; "else";
    "family"; "forall"; "foreign"; "if"; "import"; "in"; "infix"; "infixl"; "infixr"; "instance";
    "let"; "mdo"; "module"; "newtype"; "of"; "proc"; "rec"; "then"; "type"; "where"; "_"; "__";
    "as"; "qualified"; "hiding" ; "unit" ; "unsafeCoerce" ]
  Id.Set.empty

let pp_comment s = str "-- " ++ s ++ fnl ()
let pp_bracket_comment s = str"{- " ++ hov 0 s ++ str" -}"

(* Note: do not shorten [str "foo" ++ fnl ()] into [str "foo\n"],
   the '\n' character interacts badly with the Format boxing mechanism *)

let preamble table mod_name comment used_modules usf =
  let pp_import mp = str ("import qualified "^ string_of_modfile (State.get_table table) mp) ++ fnl ()
  in
  (if not (usf.magic || usf.tunknown) then mt ()
   else
     str "{-# OPTIONS_GHC -cpp -XMagicHash #-}" ++ fnl () ++
     str "{- For Hugs, use the option -F\"cpp -P -traditional\" -}" ++ fnl2 ())
  ++
  (match comment with
    | None -> mt ()
    | Some com -> pp_bracket_comment com ++ fnl2 ())
  ++
  str "module " ++ pr_upper_id mod_name ++ str " where" ++ fnl2 () ++
  str "import qualified Prelude" ++ fnl () ++
  prlist pp_import used_modules ++ fnl ()
  ++
  (if not (usf.magic || usf.tunknown) then mt ()
   else
     str "#ifdef __GLASGOW_HASKELL__" ++ fnl () ++
     str "import qualified GHC.Base" ++ fnl () ++
     str "#if __GLASGOW_HASKELL__ >= 900" ++ fnl () ++
     str "import qualified GHC.Exts" ++ fnl () ++
     str "#endif" ++ fnl () ++
     str "#else" ++ fnl () ++
     str "-- HUGS" ++ fnl () ++
     str "import qualified IOExts" ++ fnl () ++
     str "#endif" ++ fnl2 ())
  ++
  (if not usf.magic then mt ()
   else
     str "#ifdef __GLASGOW_HASKELL__" ++ fnl () ++
     str "unsafeCoerce :: a -> b" ++ fnl () ++
     str "#if __GLASGOW_HASKELL__ >= 900" ++ fnl () ++
     str "unsafeCoerce = GHC.Exts.unsafeCoerce#" ++ fnl () ++
     str "#else" ++ fnl () ++
     str "unsafeCoerce = GHC.Base.unsafeCoerce#" ++ fnl () ++
     str "#endif" ++ fnl () ++
     str "#else" ++ fnl () ++
     str "-- HUGS" ++ fnl () ++
     str "unsafeCoerce :: a -> b" ++ fnl () ++
     str "unsafeCoerce = IOExts.unsafeCoerce" ++ fnl () ++
     str "#endif" ++ fnl2 ())
  ++
  (if not usf.tunknown then mt ()
   else
     str "#ifdef __GLASGOW_HASKELL__" ++ fnl () ++
     str "type Any = GHC.Base.Any" ++ fnl () ++
     str "#else" ++ fnl () ++
     str "-- HUGS" ++ fnl () ++
     str "type Any = ()" ++ fnl () ++
     str "#endif" ++ fnl2 ())
  ++
  (if not usf.mldummy then mt ()
   else
     str "__ :: any" ++ fnl () ++
     str "__ = Prelude.error \"Logical or arity value used\"" ++ fnl2 ())

let pp_abst = function
  | [] -> (mt ())
  | l  -> (str "\\" ++
             prlist_with_sep (fun () -> (str " ")) Id.print l ++
             str " ->" ++ spc ())

(*s The pretty-printer for haskell syntax *)

let pp_global table k r =
  if is_inline_custom r then str (find_custom r)
  else str (Common.pp_global table k r)

(*s Pretty-printing of types. [par] is a boolean indicating whether parentheses
    are needed or not. *)

let rec pp_type table par vl t =
  let rec pp_rec par = function
    | Tmeta _ | Tvar' _ -> assert false
    | Tvar i ->
      (try Id.print (List.nth vl (pred i))
       with Failure _ -> (str "a" ++ int i))
    | Tglob (r,[]) -> pp_global table Type r
    | Tglob (gr,l)
        when not (keep_singleton ()) && Rocqlib.check_ref sig_type_name gr.glob ->
          pp_type table true vl (List.hd l)
    | Tglob (r,l) ->
          pp_par par
            (pp_global table Type r ++ spc () ++
             prlist_with_sep spc (pp_type table true vl) l)
    | Tarr (t1,t2) ->
        pp_par par
          (pp_rec true t1 ++ spc () ++ str "->" ++ spc () ++ pp_rec false t2)
    | Tdummy _ -> str "()"
    | Tunknown -> str "Any"
    | Taxiom -> str "() -- AXIOM TO BE REALIZED" ++ fnl ()
 in
  hov 0 (pp_rec par t)

(*s Pretty-printing of expressions. [par] indicates whether
    parentheses are needed or not. [env] is the list of names for the
    de Bruijn variables. [args] is the list of collected arguments
    (already pretty-printed). *)

let expr_needs_par = function
  | MLlam _  -> true
  | MLcase _ -> false (* now that we use the case ... of { ... } syntax *)
  | _        -> false


let rec pp_expr table par env args =
  let apply st = pp_apply st par args
  and apply2 st = pp_apply2 st par args in
  function
    | MLrel n ->
        let id = get_db_name n env in
        (* Try to survive to the occurrence of a Dummy rel.
           TODO: we should get rid of this hack (cf. BZ#592) *)
        let id = if Id.equal id dummy_name then Id.of_string "__" else id in
        apply (Id.print id)
    | MLapp (f,args') ->
        let stl = List.map (pp_expr table true env []) args' in
        pp_expr table par env (stl @ args) f
    | MLlam _ as a ->
        let fl,a' = collect_lams a in
        let fl,env' = push_vars (List.map id_of_mlid fl) env in
        let st = (pp_abst (List.rev fl) ++ pp_expr table false env' [] a') in
        apply2 st
    | MLletin (id,a1,a2) ->
        let i,env' = push_vars [id_of_mlid id] env in
        let pp_id = Id.print (List.hd i)
        and pp_a1 = pp_expr table false env [] a1
        and pp_a2 = pp_expr table (not par && expr_needs_par a2) env' [] a2 in
        let pp_def =
          str "let {" ++ cut () ++
          hov 1 (pp_id ++ str " = " ++ pp_a1 ++ str "}")
        in
        apply2 (hv 0 (hv 0 (hv 1 pp_def ++ spc () ++ str "in") ++
                       spc () ++ hov 0 pp_a2))
    | MLglob r ->
        apply (pp_global table Term r)
    | MLcons (_,r,a) as c ->
        assert (List.is_empty args);
        begin match a with
          | _ when is_native_char c -> pp_native_char c
          | _ when is_native_string c -> pp_native_string c
          | [] -> pp_global table Cons r
          | [a] ->
            pp_par par (pp_global table Cons r ++ spc () ++ pp_expr table true env [] a)
          | _ ->
            pp_par par (pp_global table Cons r ++ spc () ++
                        prlist_with_sep spc (pp_expr table true env []) a)
        end
    | MLtuple l ->
        assert (List.is_empty args);
        pp_boxed_tuple (pp_expr table true env []) l
    | MLcase (_,t, pv) when is_custom_match pv ->
        if not (is_regular_match pv) then
          user_err Pp.(str "Cannot mix yet user-given match and general patterns.");
        let mkfun (ids,_,e) =
          if not (List.is_empty ids) then named_lams (List.rev ids) e
          else dummy_lams (ast_lift 1 e) 1
        in
        let pp_branch tr = pp_expr table true env [] (mkfun tr) ++ fnl () in
        let inner =
          str (find_custom_match pv) ++ fnl () ++
          prvect pp_branch pv ++
          pp_expr table true env [] t
        in
        apply2 (hov 2 inner)
    | MLcase (typ,t,pv) ->
        apply2
          (v 0 (str "case " ++ pp_expr table false env [] t ++ str " of {" ++
                fnl () ++ pp_pat table env pv))
    | MLfix (i,ids,defs) ->
        let ids',env' = push_vars (List.rev (Array.to_list ids)) env in
        pp_fix table par env' i (Array.of_list (List.rev ids'),defs) args
    | MLexn s ->
        (* An [MLexn] may be applied, but I don't really care. *)
        pp_par par (str "Prelude.error" ++ spc () ++ qs s)
    | MLdummy k ->
        (* An [MLdummy] may be applied, but I don't really care. *)
        (match msg_of_implicit k with
         | "" -> str "__"
         | s -> str "__" ++ spc () ++ pp_bracket_comment (str s))
    | MLmagic a ->
        pp_apply (str "unsafeCoerce") par (pp_expr table true env [] a :: args)
    | MLaxiom s -> pp_par par (str "Prelude.error \"AXIOM TO BE REALIZED (" ++ str s ++ str ")\"")
    | MLuint _ ->
      pp_par par (str "Prelude.error \"EXTRACTION OF UINT NOT IMPLEMENTED\"")
    | MLfloat _ ->
      pp_par par (str "Prelude.error \"EXTRACTION OF FLOAT NOT IMPLEMENTED\"")
    | MLstring _ ->
      pp_par par (str "Prelude.error \"EXTRACTION OF STRING NOT IMPLEMENTED\"")
    | MLparray _ ->
      pp_par par (str "Prelude.error \"EXTRACTION OF ARRAY NOT IMPLEMENTED\"")

and pp_cons_pat table par r ppl =
  pp_par par
    (pp_global table Cons r ++ space_if (not (List.is_empty ppl)) ++ prlist_with_sep spc identity ppl)

and pp_gen_pat table par ids env = function
  | Pcons (r,l) -> pp_cons_pat table par r (List.map (pp_gen_pat table true ids env) l)
  | Pusual r -> pp_cons_pat table par r (List.map Id.print ids)
  | Ptuple l -> pp_boxed_tuple (pp_gen_pat table false ids env) l
  | Pwild -> str "_"
  | Prel n -> Id.print (get_db_name n env)

and pp_one_pat table env (ids,p,t) =
  let ids',env' = push_vars (List.rev_map id_of_mlid ids) env in
  hov 2 (str " " ++
         pp_gen_pat table false (List.rev ids') env' p ++
         str " ->" ++ spc () ++
         pp_expr table (expr_needs_par t) env' [] t)

and pp_pat table env pv =
  prvecti
    (fun i x ->
       pp_one_pat table env pv.(i) ++
       if Int.equal i (Array.length pv - 1) then str "}" else
         (str ";" ++ fnl ()))
    pv

(*s names of the functions ([ids]) are already pushed in [env],
    and passed here just for convenience. *)

and pp_fix table par env i (ids,bl) args =
  pp_par par
    (v 0
       (v 1 (str "let {" ++ fnl () ++
             prvect_with_sep (fun () -> str ";" ++ fnl ())
               (fun (fi,ti) -> pp_function table env (Id.print fi) ti)
               (Array.map2 (fun a b -> a,b) ids bl) ++
             str "}") ++
        fnl () ++ str "in " ++ pp_apply (Id.print ids.(i)) false args))

and pp_function table env f t =
  let bl,t' = collect_lams t in
  let bl,env' = push_vars (List.map id_of_mlid bl) env in
  (f ++ pr_binding (List.rev bl) ++
     str " =" ++ fnl () ++ str "  " ++
     hov 2 (pp_expr table false env' [] t'))

(*s Pretty-printing of inductive types declaration. *)

let pp_logical_ind packet =
  pp_bracket_comment
    (Id.print packet.ip_typename ++ str " : logical inductive" ++ fnl () ++
     str "with constructors : " ++ prvect_with_sep spc Id.print packet.ip_consnames)

let pp_singleton table packet =
  let name = pp_global table Type packet.ip_typename_ref in
  let l = rename_tvars keywords packet.ip_vars in
  hov 2 (str "type " ++ name ++ spc () ++
         prlist_with_sep spc Id.print l ++
         (if not (List.is_empty l) then str " " else mt ()) ++ str "=" ++ spc () ++
         pp_type table false l (List.hd packet.ip_types.(0)) ++ fnl () ++
         pp_comment (str "singleton inductive, whose constructor was " ++
                     Id.print packet.ip_consnames.(0)))

let pp_one_ind table p pl cv =
  let pl = rename_tvars keywords pl in
  let pp_constructor (r,l) =
    (pp_global table Cons r ++
     match l with
       | [] -> (mt ())
       | _  -> (str " " ++
                prlist_with_sep
                  (fun () -> (str " ")) (pp_type table true pl) l))
  in
  str (if Array.is_empty cv then "type " else "data ") ++
  pp_global table Type p.ip_typename_ref ++
  prlist_strict (fun id -> str " " ++ pr_lower_id id) pl ++ str " =" ++
  if Array.is_empty cv then str " () -- empty inductive"
  else
    (fnl () ++ str " " ++
     v 0 (str "  " ++
          prvect_with_sep (fun () -> fnl () ++ str "| ") pp_constructor
            (Array.mapi (fun i c -> p.ip_consnames_ref.(i), c) cv)))

let rec pp_ind table first i ind =
  if i >= Array.length ind.ind_packets then
    if first then mt () else fnl ()
  else
    let p = ind.ind_packets.(i) in
    let ip = p.ip_typename_ref in
    if is_custom ip then pp_ind table first (i+1) ind
    else
      if p.ip_logical then
        pp_logical_ind p ++ pp_ind table first (i+1) ind
      else
        pp_one_ind table p p.ip_vars p.ip_types ++ fnl () ++
        pp_ind table false (i+1) ind


(*s Pretty-printing of a declaration. *)

let pp_decl table = function
  | Dind i when i.ind_kind == Singleton ->
      pp_singleton table i.ind_packets.(0) ++ fnl ()
  | Dind i -> hov 0 (pp_ind table true 0 i)
  | Dtype (r, l, t) ->
      if is_inline_custom r then mt ()
      else
        let l = rename_tvars keywords l in
        let st =
          try
            let ids,s = find_type_custom r in
            prlist (fun id -> str (id^" ")) ids ++ str "=" ++ spc () ++ str s
          with Not_found ->
            prlist (fun id -> Id.print id ++ str " ") l ++
            if t == Taxiom then str "= () -- AXIOM TO BE REALIZED" ++ fnl ()
            else str "=" ++ spc () ++ pp_type table false l t
        in
        hov 2 (str "type " ++ pp_global table Type r ++ spc () ++ st) ++ fnl2 ()
  | Dfix (rv, defs, typs) ->
      let names = Array.map
        (fun r -> if is_inline_custom r then mt () else pp_global table Term r) rv
      in
      prvecti
        (fun i r ->
          let void = is_inline_custom r ||
            (not (is_custom r) &&
             match defs.(i) with MLexn "UNUSED" -> true | _ -> false)
          in
          if void then mt ()
          else
            hov 2 (names.(i) ++ str " :: " ++ pp_type table false [] typs.(i)) ++ fnl () ++
            (if is_custom r then
                (names.(i) ++ str " = " ++ str (find_custom r))
             else
                (pp_function table (empty_env table ()) names.(i) defs.(i)))
            ++ fnl2 ())
        rv
  | Dterm (r, a, t) ->
      if is_inline_custom r then mt ()
      else
        let e = pp_global table Term r in
        hov 2 (e ++ str " :: " ++ pp_type table false [] t) ++ fnl () ++
          if is_custom r then
            hov 0 (e ++ str " = " ++ str (find_custom r) ++ fnl2 ())
          else
            hov 0 (pp_function table (empty_env table ()) e a ++ fnl2 ())

let rec pp_structure_elem table = function
  | (l,SEdecl d) -> pp_decl table d
  | (l,SEmodule m) -> pp_module_expr table m.ml_mod_expr
  | (l,SEmodtype m) -> mt ()
      (* for the moment we simply discard module type *)

and pp_module_expr table = function
  | MEstruct (mp,sel) -> prlist_strict (fun e -> pp_structure_elem table e) sel
  | MEfunctor _ -> mt ()
      (* for the moment we simply discard unapplied functors *)
  | MEident _ | MEapply _ -> assert false
      (* should be expanded in extract_env *)

let pp_struct table =
  let pp_sel (mp,sel) = State.with_visibility table mp [] begin fun table ->
    prlist_strict (fun e -> pp_structure_elem table e) sel
  end in
  prlist_strict pp_sel

let file_naming state mp = file_of_modfile (State.get_table state) mp

let haskell_descr = {
  keywords = keywords;
  file_suffix = ".hs";
  file_naming = file_naming;
  preamble = preamble;
  pp_struct = pp_struct;
  sig_suffix = None;
  sig_preamble = (fun _ _ _ _ _ -> mt ());
  pp_sig = (fun _ _ -> mt ());
  pp_decl = pp_decl;
}
