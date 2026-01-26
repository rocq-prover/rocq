(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open Util
open CAst
open CErrors
open Names
open Libnames
open Libobject
open Nametab
open Tac2expr
open Tac2print
open Tac2intern
open Tac2subst

(** Grammar entries *)

module Pltac =
struct
let ltac2_expr = Tac2syn.Internal.ltac2_expr
let tac2expr_in_env = Procq.Entry.make "tac2expr_in_env"

let q_ident = Procq.Entry.make "q_ident"
let q_bindings = Procq.Entry.make "q_bindings"
let q_with_bindings = Procq.Entry.make "q_with_bindings"
let q_intropattern = Procq.Entry.make "q_intropattern"
let q_intropatterns = Procq.Entry.make "q_intropatterns"
let q_destruction_arg = Procq.Entry.make "q_destruction_arg"
let q_induction_clause = Procq.Entry.make "q_induction_clause"
let q_conversion = Procq.Entry.make "q_conversion"
let q_orient = Procq.Entry.make "q_orient"
let q_rewriting = Procq.Entry.make "q_rewriting"
let q_clause = Procq.Entry.make "q_clause"
let q_dispatch = Procq.Entry.make "q_dispatch"
let q_occurrences = Procq.Entry.make "q_occurrences"
let q_reference = Procq.Entry.make "q_reference"
let q_strategy_flag = Procq.Entry.make "q_strategy_flag"
let q_constr_matching = Procq.Entry.make "q_constr_matching"
let q_goal_matching = Procq.Entry.make "q_goal_matching"
let q_hintdb = Procq.Entry.make "q_hintdb"
let q_move_location = Procq.Entry.make "q_move_location"
let q_pose = Procq.Entry.make "q_pose"
let q_assert = Procq.Entry.make "q_assert"
end

let () =
  let entries = [
    Procq.Entry.Any Pltac.ltac2_expr;
  ] in
  Procq.register_grammars_by_name "ltac2" entries

(** Tactic definition *)

type tacdef = {
  tacdef_local : bool;
  tacdef_mutable : bool;
  tacdef_expr : glb_tacexpr;
  tacdef_type : type_scheme;
  tacdef_deprecation : Deprecation.t option;
}

let define_tacdef ((_,kn), def) =
  let data = {
    Tac2env.gdata_expr = def.tacdef_expr;
    gdata_type = def.tacdef_type;
    gdata_mutable = def.tacdef_mutable;
    gdata_deprecation = def.tacdef_deprecation;
    gdata_mutation_history = [];
  } in
  Tac2env.define_global kn data

let push_tacdef visibility ((sp, kn), def) =
  if not def.tacdef_local then Tac2env.push_ltac visibility sp (TacConstant kn)

let load_tacdef i obj =
  push_tacdef (Until i) obj;
  define_tacdef obj

let open_tacdef i obj = push_tacdef (Exactly i) obj

(* Not sure if it's correct that we don't "open", do Until 1 and
   Exactly 1 have the same effect? *)
let cache_tacdef ((sp, kn), def as obj) =
  (* unconditional unlike push_tacdef *)
  Tac2env.push_ltac (Until 1) sp (TacConstant kn);
  define_tacdef obj

let subst_tacdef (subst, def) =
  let expr' = subst_expr subst def.tacdef_expr in
  let type' = subst_type_scheme subst def.tacdef_type in
  if expr' == def.tacdef_expr && type' == def.tacdef_type then def
  else { def with tacdef_expr = expr'; tacdef_type = type' }

let classify_tacdef o = Substitute

let inTacDef : Id.t -> tacdef -> obj =
  declare_named_object {(default_object "TAC2-DEFINITION") with
     cache_function  = cache_tacdef;
     load_function   = load_tacdef;
     open_function   = filtered_open open_tacdef;
     subst_function = subst_tacdef;
     classify_function = classify_tacdef}

(** Type definition *)

type typdef = {
  typdef_local : bool;
  typdef_abstract : bool;
  typdef_expr : glb_quant_typedef;
}

let change_kn_label kn id =
  let mp = KerName.modpath kn in
  KerName.make mp id

let change_sp_label sp id =
  let (dp, _) = Libnames.repr_path sp in
  Libnames.make_path dp id

let push_typedef_contents visibility sp kn (_, def) = match def with
| GTydDef _ -> ()
| GTydAlg { galg_constructors = cstrs } ->
  (* Register constructors *)
  let iter (user_warns, c, _) =
    let spc = change_sp_label sp c in
    let knc = change_kn_label kn c in
    Tac2env.push_constructor ?user_warns visibility spc knc
  in
  List.iter iter cstrs
| GTydRec fields ->
  (* Register fields *)
  let iter (c, _, _) =
    let spc = change_sp_label sp c in
    let knc = change_kn_label kn c in
    Tac2env.push_projection visibility spc knc
  in
  List.iter iter fields
| GTydOpn -> ()

let push_typedef visibility sp kn def =
  Tac2env.push_type visibility sp kn;
  push_typedef_contents visibility sp kn def

let next i =
  let ans = !i in
  let () = incr i in
  ans

let define_typedef kn (params, def as qdef) = match def with
| GTydDef _ ->
  Tac2env.define_type kn qdef
| GTydAlg { galg_constructors = cstrs } ->
  (* Define constructors *)
  let constant = ref 0 in
  let nonconstant = ref 0 in
  let iter (_warn, c, args) =
    let knc = change_kn_label kn c in
    let tag = if List.is_empty args then next constant else next nonconstant in
    let data = {
      Tac2env.cdata_prms = params;
      cdata_type = kn;
      cdata_args = args;
      cdata_indx = Some tag;
    } in
    Tac2env.define_constructor knc data
  in
  Tac2env.define_type kn qdef;
  List.iter iter cstrs
| GTydRec fs ->
  (* Define projections *)
  let iter i (id, mut, t) =
    let knp = change_kn_label kn id in
    let proj = {
      Tac2env.pdata_prms = params;
      pdata_type = kn;
      pdata_ptyp = t;
      pdata_mutb = mut;
      pdata_indx = i;
    } in
    Tac2env.define_projection knp proj
  in
  Tac2env.define_type kn qdef;
  List.iteri iter fs
| GTydOpn ->
  Tac2env.define_type kn qdef

let perform_typdef vs ((sp, kn), def) =
  let expr = def.typdef_expr in
  let expr = if def.typdef_abstract then fst expr, GTydDef None else expr in
  let () = if not def.typdef_local then push_typedef vs sp kn expr in
  define_typedef kn expr

let load_typdef i obj = perform_typdef (Until i) obj
let open_typdef i obj = perform_typdef (Exactly i) obj

let cache_typdef ((sp, kn), def) =
  let () = push_typedef (Until 1) sp kn def.typdef_expr in
  define_typedef kn def.typdef_expr

let subst_typdef (subst, def) =
  let expr' = subst_quant_typedef subst def.typdef_expr in
  if expr' == def.typdef_expr then def else { def with typdef_expr = expr' }

let classify_typdef o = Substitute

let inTypDef : Id.t -> typdef -> obj =
  declare_named_object {(default_object "TAC2-TYPE-DEFINITION") with
     cache_function  = cache_typdef;
     load_function   = load_typdef;
     open_function   = filtered_open open_typdef;
     subst_function = subst_typdef;
     classify_function = classify_typdef}

(** Type extension *)

type extension_data = {
  edata_warn : UserWarn.t option;
  edata_name : Id.t;
  edata_args : int glb_typexpr list;
}

type typext = {
  typext_local : bool;
  typext_prms : int;
  typext_type : type_constant;
  typext_expr : extension_data list;
}

let push_typext vis prefix def =
  let iter data =
    let spc = Libnames.add_path_suffix prefix.obj_path data.edata_name in
    let knc = KerName.make prefix.obj_mp data.edata_name in
    let user_warns = data.edata_warn in
    Tac2env.push_constructor ?user_warns vis spc knc
  in
  List.iter iter def.typext_expr

let define_typext mp def =
  let iter data =
    let knc = KerName.make mp data.edata_name in
    let cdata = {
      Tac2env.cdata_prms = def.typext_prms;
      cdata_type = def.typext_type;
      cdata_args = data.edata_args;
      cdata_indx = None;
    } in
    Tac2env.define_constructor knc cdata
  in
  List.iter iter def.typext_expr

let cache_typext (prefix, def) =
  let () = define_typext prefix.obj_mp def in
  push_typext (Until 1) prefix def

let perform_typext vs (prefix, def) =
  let () = if not def.typext_local then push_typext vs prefix def in
  define_typext prefix.obj_mp def

let load_typext i obj = perform_typext (Until i) obj
let open_typext i obj = perform_typext (Exactly i) obj

let subst_typext (subst, e) =
  let open Mod_subst in
  let subst_data data =
    let edata_args = List.Smart.map (fun e -> subst_type subst e) data.edata_args in
    if edata_args == data.edata_args then data
    else { data with edata_args }
  in
  let typext_type = subst_kn subst e.typext_type in
  let typext_expr = List.Smart.map subst_data e.typext_expr in
  if typext_type == e.typext_type && typext_expr == e.typext_expr then
    e
  else
    { e with typext_type; typext_expr }

let classify_typext o = Substitute

let inTypExt : typext -> obj =
  declare_named_object_gen {(default_object "TAC2-TYPE-EXTENSION") with
     cache_function  = cache_typext;
     load_function   = load_typext;
     open_function   = filtered_open open_typext;
     subst_function = subst_typext;
     classify_function = classify_typext}

(** Toplevel entries *)

(** Mangle recursive tactics *)
let inline_rec_tactic tactics =
  let map (id, e) =
    let map_body ({loc;v=id}, e) = CAst.(make ?loc @@ CPatVar (Name id)), e in
    let bnd = List.map map_body tactics in
    let var_of_id {loc;v=id} =
      let qid = qualid_of_ident ?loc id in
      CAst.make ?loc @@ CTacRef (RelId qid)
    in
    let loc0 = e.loc in
    let e = CAst.make ?loc:loc0 @@ CTacLet (true, bnd, var_of_id id) in
    (id, e)
  in
  List.map map tactics

let check_lowercase {loc;v=id} =
  if Tac2env.is_constructor (Libnames.qualid_of_ident id) then
    user_err ?loc (str "The identifier " ++ Id.print id ++ str " must start with a lowercase letter.")

let check_uppercase {loc;v=id} =
  if not @@ Tac2env.is_constructor (Libnames.qualid_of_ident id) then
    user_err ?loc (str "The identifier " ++ Id.print id ++ str " must start with an uppercase letter.")

let pp_not_value_reason = function
  | MutString -> str "(it contains a string literal, and strings are mutable)"
  | Application -> str "(it contains an application)"
  | MutDef kn -> str "(it contains mutable definition " ++ pr_tacref Id.Set.empty kn
  | MutCtor kn -> str "(it contains a constructor of type " ++ pr_typref kn ++ str " which has mutable fields)"
  | MutProj kn -> str "(it contains a mutable projection from type " ++ pr_typref kn ++ str ")"
  | MaybeValButNotSupported -> mt()

let check_value ?loc e =
  match check_value e with
  | None -> ()
  | Some reason ->
    let ppreason = pp_not_value_reason reason in
    user_err ?loc
      (str "Tactic definition must be a syntactical value" ++
       (if ismt ppreason then mt() else spc() ++ ppreason) ++ str "." ++ spc() ++
       str "Consider using a thunk.")

let check_ltac_exists {loc;v=id} =
  let kn = Lib.make_kn id in
  let exists =
    try let _ = Tac2env.interp_global kn in true with Not_found -> false
  in
  if exists then
    user_err ?loc (str "Tactic " ++ Names.Id.print id ++ str " already exists")


let register_ltac ?deprecation ?(local = false) ?(mut = false) isrec tactics =
  let map ({loc;v=na}, e) =
    let id = match na with
    | Anonymous ->
      user_err ?loc (str "Tactic definition must have a name")
    | Name id -> id
    in
    let () = check_lowercase CAst.(make ?loc id) in
    (CAst.(make ?loc id), e)
  in
  let tactics = List.map map tactics in
  let tactics =
    if isrec then inline_rec_tactic tactics else tactics
  in
  let map (lid, ({loc=eloc} as e)) =
    let (e, t) = intern ~strict:true [] e in
    let () = check_value ?loc:eloc e in
    let () = check_ltac_exists lid in
    (lid.v, e, t)
  in
  let defs = List.map map tactics in
  let iter (id, e, t) =
    let def = {
      tacdef_local = local;
      tacdef_mutable = mut;
      tacdef_expr = e;
      tacdef_type = t;
      tacdef_deprecation = deprecation;
    } in
    Lib.add_leaf (inTacDef id def)
  in
  List.iter iter defs

let qualid_to_ident qid =
  if qualid_is_ident qid then CAst.make ?loc:qid.CAst.loc @@ qualid_basename qid
  else user_err ?loc:qid.CAst.loc (str "Identifier expected")

let register_typedef ?(local = false) ?(abstract=false) isrec types =
  let same_name ({v=id1}, _) ({v=id2}, _) = Id.equal id1 id2 in
  let () = match List.duplicates same_name types with
  | [] -> ()
  | ({loc;v=id}, _) :: _ ->
    user_err ?loc (str "Multiple definition of the type name " ++ Id.print id)
  in
  let () =
    let check_existing_type ({v=id},_) =
      let (_, kn) = Lib.make_foname id in
      try let _ = Tac2env.interp_type kn in
        user_err (str "Multiple definition of the type name " ++ Id.print id)
      with Not_found -> ()
    in
    List.iter check_existing_type types
  in
  let check ({loc;v=id}, (params, def)) =
    let same_name {v=id1} {v=id2} = Id.equal id1 id2 in
    let () = match List.duplicates same_name params with
    | [] -> ()
    | {loc;v=id} :: _ ->
      user_err ?loc (str "The type parameter " ++ Id.print id ++
        str " occurs several times")
    in
    match def with
    | CTydDef _ ->
      if isrec then
        user_err ?loc (str "The type abbreviation " ++ Id.print id ++
          str " cannot be recursive")
    | CTydAlg cs ->
      let same_name (_, id1, _) (_, id2, _) = Id.equal id1.v id2.v in
      let () = match List.duplicates same_name cs with
      | [] -> ()
      | (_, id, _) :: _ ->
        user_err (str "Multiple definitions of the constructor " ++ Id.print id.v)
      in
      let () = List.iter (fun (_,id,_) -> check_uppercase id) cs in
      let () =
        let check_existing_ctor (_, id, _) =
          let (_, kn) = Lib.make_foname id.v in
          try let _ = Tac2env.interp_constructor kn in
            user_err (str "Constructor already defined in this module " ++ Id.print id.v)
          with Not_found -> ()
        in
        List.iter check_existing_ctor cs
      in
      ()
    | CTydRec ps ->
      let same_name (id1, _, _) (id2, _, _) = Id.equal id1 id2 in
      let () = match List.duplicates same_name ps with
      | [] -> ()
      | (id, _, _) :: _ ->
        user_err (str "Multiple definitions of the projection " ++ Id.print id)
      in
      ()
    | CTydOpn ->
      if isrec then
        user_err ?loc (str "The open type declaration " ++ Id.print id ++
                       str " cannot be recursive");
      if abstract then
        (* Naive implementation allows to use and match on already
           existing constructors but not declare new ones outside the
           type's origin module. Not sure that's what we want so
           forbid it for now. *)
        user_err ?loc (str "Open types currently do not support #[abstract].")
  in
  let () = List.iter check types in
  let self =
    if isrec then
      let fold accu ({v=id}, (params, _)) =
        Id.Map.add id (Lib.make_kn id, List.length params) accu
      in
      List.fold_left fold Id.Map.empty types
    else Id.Map.empty
  in
  let map ({v=id}, def) =
    let typdef = {
      typdef_local = local;
      typdef_abstract = abstract;
      typdef_expr = intern_typedef self def;
    } in
    (id, typdef)
  in
  let types = List.map map types in
  let iter (id, def) = Lib.add_leaf (inTypDef id def) in
  List.iter iter types

let register_primitive ?deprecation ?(local = false) ({loc;v=id} as lid) t ml =
  let () = check_ltac_exists lid in
  let t = intern_open_type t in
  let () =
    try let _ = Tac2env.interp_primitive ml in () with Not_found ->
      user_err ?loc (str "Unregistered primitive " ++
        quote (str ml.mltac_plugin) ++ spc () ++ quote (str ml.mltac_tactic))
  in
  let e = GTacPrm ml in
  let def = {
    tacdef_local = local;
    tacdef_mutable = false;
    tacdef_expr = e;
    tacdef_type = t;
    tacdef_deprecation = deprecation;
  } in
  Lib.add_leaf (inTacDef id def)

let register_open ?(local = false) qid (params, def) =
  let kn =
    try Tac2env.locate_type qid
    with Not_found ->
      user_err ?loc:qid.CAst.loc (str "Unbound type " ++ pr_qualid qid)
  in
  let (tparams, t) = Tac2env.interp_type kn in
  let () = match t with
  | GTydOpn -> ()
  | GTydAlg _ | GTydRec _ | GTydDef _ ->
    user_err ?loc:qid.CAst.loc (str "Type " ++ pr_qualid qid ++ str " is not an open type")
  in
  let () =
    if not (Int.equal (List.length params) tparams) then
      Tac2intern.error_nparams_mismatch ?loc:qid.CAst.loc (List.length params) tparams
  in
  match def with
  | CTydOpn -> ()
  | CTydAlg def ->
    let () =
      let same_name (_, id1, _) (_, id2, _) = Id.equal id1.v id2.v in
      let () = match List.duplicates same_name def with
        | [] -> ()
        | (_, id, _) :: _ ->
          user_err (str "Multiple definitions of the constructor " ++ Id.print id.v)
      in
      let check_existing_ctor (_, id, _) =
          let (_, kn) = Lib.make_foname id.v in
          try let _ = Tac2env.interp_constructor kn in
            user_err (str "Constructor already defined in this module " ++ Id.print id.v)
          with Not_found -> ()
      in
      let () = List.iter check_existing_ctor def in
      ()
    in
    let intern_type t =
      let tpe = CTydDef (Some t) in
      let (_, ans) = intern_typedef Id.Map.empty (params, tpe) in
      match ans with
      | GTydDef (Some t) -> t
      | _ -> assert false
    in
    let map (atts, id, tpe) =
      let () = check_uppercase id in
      let warn = Attributes.parse Attributes.user_warns atts in
      let tpe = List.map intern_type tpe in
      { edata_warn = warn; edata_name = id.v; edata_args = tpe }
    in
    let def = List.map map def in
    let def = {
      typext_local = local;
      typext_type = kn;
      typext_prms = tparams;
      typext_expr = def;
    } in
    Lib.add_leaf (inTypExt def)
  | CTydRec _ | CTydDef _ ->
    user_err ?loc:qid.CAst.loc (str "Extensions only accept inductive constructors")

let register_type ?local ?abstract isrec types = match types with
| [qid, true, def] ->
  let () = if isrec then user_err ?loc:qid.CAst.loc (str "Extensions cannot be recursive.") in
  let () = if Option.default false abstract
    then user_err ?loc:qid.loc (str "Extensions cannot be abstract.")
  in
  register_open ?local qid def
| _ ->
  let map (qid, redef, def) =
    let () = if redef then
      user_err ?loc:qid.loc (str "Types can only be extended one by one")
    in
    (qualid_to_ident qid, def)
  in
  let types = List.map map types in
  register_typedef ?local ?abstract isrec types

let load_import_type i ((sp,kn),orig) =
  let def = Tac2env.interp_type orig in
  push_typedef_contents (Until i) sp orig def

let open_import_type i ((sp,kn),orig) =
  let def = Tac2env.interp_type orig in
  push_typedef_contents (Exactly i) sp orig def

let cache_import_type o = load_import_type 1 o

let inImportType =
  declare_named_object
    { (default_object "TAC2-IMPORT-TYPE") with
     cache_function = cache_import_type;
     load_function = load_import_type;
     open_function = filtered_open open_import_type;
     subst_function = (fun (subst,kn) -> Mod_subst.subst_kn subst kn);
     (* NB don't bother supporting Local as it doesn't seem useful *)
     classify_function = (fun _ -> Substitute);
    }

(* TODO deprecate attr *)
let import_type qid as_id =
  let () =
    if Lib.sections_are_opened() then
      (* if you want to implement it take care that the "orig" type isn't local to the section *)
      CErrors.user_err Pp.(str "Ltac2 Import Type not supported in sections.")
  in
  match Tac2env.locate_type qid with
  | exception Not_found ->
    CErrors.user_err ?loc:qid.loc Pp.(str "Unknown Ltac2 type " ++ pr_qualid qid ++ str ".")
  | orig ->
    let params, _ = Tac2env.interp_type orig in
    let alias_def = GTypRef (Other orig, List.init params (fun i -> GTypVar i)) in
    Lib.add_leaf (inTypDef as_id {
        typdef_local = false;
        typdef_abstract = false;
        typdef_expr = params, GTydDef (Some alias_def);
      });
    Lib.add_leaf (inImportType as_id orig)

(** {5 Parsing} *)

type abbreviation = {
  abbr_body : raw_tacexpr;
  abbr_depr : Deprecation.t option;
}

let perform_abbreviation visibility ((sp, kn), abbr) =
  let () = Tac2env.push_ltac visibility sp (TacAlias kn) in
  Tac2env.define_alias ?deprecation:abbr.abbr_depr kn abbr.abbr_body

let load_abbreviation i obj = perform_abbreviation (Until i) obj
let open_abbreviation i obj = perform_abbreviation (Exactly i) obj

let cache_abbreviation ((sp, kn), abbr) =
  let () = Tac2env.push_ltac (Until 1) sp (TacAlias kn) in
  Tac2env.define_alias ?deprecation:abbr.abbr_depr kn abbr.abbr_body

let subst_abbreviation (subst, abbr) =
  let body' = subst_rawexpr subst abbr.abbr_body in
  if body' == abbr.abbr_body then abbr
  else { abbr_body = body'; abbr_depr = abbr.abbr_depr }

let inTac2Abbreviation : Id.t -> abbreviation -> Libobject.obj =
  let open Libobject in
  declare_named_object {(default_object "TAC2-ABBREVIATION") with
     cache_function  = cache_abbreviation;
     load_function   = load_abbreviation;
     open_function   = filtered_open ~cat:Tac2syn.ltac2_notation_cat open_abbreviation;
     subst_function = subst_abbreviation;
     classify_function = (fun _ -> Substitute);
}

type 'body notation_interpretation_data =
| Abbreviation of Id.t * Deprecation.t option * 'body
| Synext of 'body Tac2syn.notation_interpretation

let pr_register_abbreviation id body =
  let open Pp in
  Id.print id.CAst.v ++
  hov 2 (str ":= " ++ Tac2print.pr_rawexpr_gen E5 ~avoid:Id.Set.empty body)

let register_abbreviation atts id body =
  let deprecation = Attributes.(parse deprecation) atts in
  let () = check_lowercase id in
  Abbreviation(id.CAst.v, deprecation, body)

let warn_deprecated_notation_for_abbreviation =
    CWarnings.create ~name:"ltac2-notation-for-abbreviation" ~category:Deprecation.Version.v9_2
      Pp.(fun () -> strbrk "Use of \"Ltac2 Notation\" keyword for abbreviations is deprecated, use \"Ltac2 Abbreviation\" instead.")

let is_abbrev_target target =
  let open Tac2syn in
  Option.is_empty target.target_entry && Option.is_empty target.target_level

let register_notation atts tkn target body =
  match tkn, is_abbrev_target target with
  | [SexprRec (_, {loc;v=Some id}, [])], true ->
    warn_deprecated_notation_for_abbreviation ();
    let id = if qualid_is_ident id then qualid_basename id
      else CErrors.user_err ?loc:id.loc Pp.(str "Must be an identifier.")
    in
    register_abbreviation atts CAst.(make ?loc id) body
  | _ ->
    let data = Tac2syn.register_notation atts tkn target body in
    Synext data

let register_notation_interpretation = function
  | Abbreviation (id, deprecation, body) ->
    let body = Tac2intern.globalize Id.Set.empty body in
    let abbr = { abbr_body = body; abbr_depr = deprecation } in
    Lib.add_leaf (inTac2Abbreviation id abbr)
  | Synext data ->
    let data = Tac2syn.intern_notation_interpretation intern_notation_data data in
    Tac2syn.register_notation_interpretation data

(** {5 Redefinition} *)

type redefinition = {
  redef_local : Libobject.locality;
  redef_kn : ltac_constant;
  redef_body : glb_tacexpr;
  redef_old : Id.t option;
}

let perform_redefinition (prefix,redef) =
  let kn = redef.redef_kn in
  let data = Tac2env.interp_global kn in
  let body = match redef.redef_old with
  | None -> redef.redef_body
  | Some id ->
    (* Rebind the old value with a let-binding *)
    GTacLet (false, [Name id, data.Tac2env.gdata_expr], redef.redef_body)
  in
  let history = if Option.has_some redef.redef_old then data.gdata_mutation_history else [] in
  let data = {
    data with
    gdata_expr = body;
    gdata_mutation_history = prefix.Libobject.obj_mp :: history;
  }
  in
  Tac2env.define_global kn data

let load_redefinition _ (_,redef as o) =
  match redef.redef_local with
  | Local -> assert false
  | Export -> ()
  | SuperGlobal -> perform_redefinition o

let open_redefinition (_,redef as o) =
  match redef.redef_local with
  | Local -> assert false
  | Export -> perform_redefinition o
  | SuperGlobal -> ()

let subst_redefinition (subst, redef) =
  let kn = Mod_subst.subst_kn subst redef.redef_kn in
  let body = subst_expr subst redef.redef_body in
  if kn == redef.redef_kn && body == redef.redef_body then redef
  else { redef_local = redef.redef_local;
         redef_kn = kn;
         redef_body = body;
         redef_old = redef.redef_old;
       }

let classify_redefinition o = match o.redef_local with
  | Local -> Dispose
  | Export | SuperGlobal -> Substitute

let inTac2Redefinition : redefinition -> obj =
  declare_named_object_gen
    {(default_object "TAC2-REDEFINITION") with
     cache_function  = perform_redefinition;
     load_function = load_redefinition;
     open_function   = simple_open open_redefinition;
     subst_function = subst_redefinition;
     classify_function = classify_redefinition;
    }

let register_redefinition ~local qid old ({loc=eloc} as e) =
  let local = match local with
    | None -> if Lib.sections_are_opened() then Local else Export
    | Some local -> Locality.check_locality_nodischarge Local; local
  in
  let kn =
    try Tac2env.locate_ltac qid
    with Not_found -> user_err ?loc:qid.CAst.loc (str "Unknown tactic " ++ pr_qualid qid)
  in
  let kn = match kn with
  | TacConstant kn -> kn
  | TacAlias _ ->
    user_err ?loc:qid.CAst.loc (str "Cannot redefine syntactic abbreviations")
  in
  let data = Tac2env.interp_global kn in
  let () =
    if not (data.Tac2env.gdata_mutable) then
      user_err ?loc:qid.CAst.loc (str "The tactic " ++ pr_qualid qid ++ str " is not declared as mutable")
  in
  let ctx = match old with
  | None -> []
  | Some { CAst.v = id } -> [id, data.Tac2env.gdata_type]
  in
  let (e, t) = intern ~strict:true ctx e in
  let () = check_value ?loc:eloc e in
  let () =
    if not (Tac2intern.check_subtype t data.Tac2env.gdata_type) then
      let name = int_name () in
      user_err ?loc:qid.CAst.loc (str "Type " ++ pr_glbtype name (snd t) ++
        str " is not a subtype of " ++ pr_glbtype name (snd data.Tac2env.gdata_type))
  in
  let old = Option.map (fun { CAst.v = id } -> id) old in
  let def = {
    redef_local = local;
    redef_kn = kn;
    redef_body = e;
    redef_old = old;
  } in
  Lib.add_leaf (inTac2Redefinition def)

let perform_eval ~pstate e =
  let env = Global.env () in
  let (e, ty) = Tac2intern.intern ~strict:false [] e in
  let v = Tac2interp.interp Tac2interp.empty_environment e in
  let proof =
    match pstate with
    | None ->
      let sigma = Evd.from_env env in
      let name = Id.of_string "ltac2" in
      Proof.start ~name ~poly:PolyFlags.default sigma []
    | Some pstate ->
      Declare.Proof.get pstate
  in
  let (proof, _, ans) = Proof.run_tactic (Global.env ()) v proof in
  let { Proof.sigma } = Proof.data proof in
  let name = int_name () in
  Feedback.msg_notice (str "- : " ++ pr_glbtype name (snd ty)
    ++ spc () ++  str "=" ++ spc () ++
    Tac2print.pr_valexpr env sigma ans (snd ty))

(** Toplevel entries *)

let warn_modtype = CWarnings.create ~name:"ltac2-in-modtype" ~category:CWarnings.CoreCategories.ltac2 ~default:AsError
    Pp.(fun what -> strbrk "Ltac2 " ++ str what ++ strbrk " should not be defined inside module types: functor application to arguments of this module type will be unchecked")


let check_modtype what =
  if Lib.is_modtype ()
  then warn_modtype what

let abstract_att = Attributes.bool_attribute ~name:"abstract"

let register_struct atts str = match str with
| StrVal (mut, isrec, e) ->
  check_modtype "definitions";
  let deprecation, local = Attributes.(parse Notations.(deprecation ++ locality)) atts in
  register_ltac ?deprecation ?local ~mut isrec e
| StrTyp (isrec, t) ->
  check_modtype "types";
  let local, abstract = Attributes.(parse Notations.(locality ++ abstract_att)) atts in
  register_type ?local ?abstract isrec t
| StrPrm (id, t, ml) ->
  check_modtype "externals";
  let deprecation, local = Attributes.(parse Notations.(deprecation ++ locality)) atts in
  register_primitive ?deprecation ?local id t ml
| StrMut (qid, old, e) ->
  let local = Attributes.(parse explicit_hint_locality) atts in
  register_redefinition ~local qid old e

(** Toplevel exception *)

let { Goptions.get = compact_bt } =
  Goptions.declare_bool_option_and_ref ~key:["Ltac2";"Backtrace";"Compact"] ~value:true ()

let pr_frame = function
| FrAnon e ->
  if compact_bt() then str "Call <fun>"
  else str "Call {" ++ pr_glbexpr ~avoid:Id.Set.empty e ++ str "}"
| FrLtac kn ->
  str "Call " ++ pr_tacref Id.Set.empty kn
| FrPrim ml ->
  str "Prim <" ++ str ml.mltac_plugin ++ str ":" ++ str ml.mltac_tactic ++ str ">"
| FrExtn (tag, arg) ->
  if compact_bt() then fmt "Extn <%s>" (Tac2dyn.Arg.repr tag)
  else
    let obj = Tac2env.interp_ml_object tag in
    let env = Global.env () in
    let sigma = Evd.from_env env in
    str "Extn " ++ str (Tac2dyn.Arg.repr tag) ++ str ":" ++ spc () ++
    obj.Tac2env.ml_print env sigma arg

let print_raw_error kn args =
  let t_exn = KerName.make Tac2env.rocq_prefix (Id.of_string "exn") in
  let v = Tac2ffi.of_open (kn, args) in
  let t = GTypRef (Other t_exn, []) in
  let c = Tac2print.pr_valexpr (Global.env ()) Evd.empty v t in
  hov 0 (str "Uncaught Ltac2 exception:" ++ spc () ++ hov 0 c)

let print_error kn args =
  let env = Global.env() in
  let sigma = Evd.from_env env in
  let user_print = KerName.make Tac2quote.Refs.control_prefix (Id.of_string "print_exn") in
  let user_print = Tac2interp.eval_global user_print in
  let user_print = Tac2ffi.(to_fun1 of_exn (to_option to_pp)) user_print in
  let user_print () =
    let res, _, _, _, _ =
    Proofview.apply ~name:(Id.of_string_soft "ltac2 error printing") ~poly:PolyFlags.default
      env
      (user_print (Tac2interp.LtacError (kn, args), Exninfo.null))
      (snd @@ Proofview.init sigma [])
    in
    res
  in
  match user_print() with
  | Some msg -> msg
  | None -> print_raw_error kn args
  | exception e when CErrors.noncritical e ->
    let e = Exninfo.capture e in
    let ppe = match e with
      | Tac2interp.LtacError (kn', args'), _info ->
        (* don't use iprint: high risk of looping *)
        (* XXX print the info? currently CErrors.print_extra is not exposed *)
        print_raw_error kn' args'
      | _ -> CErrors.iprint e
    in
    print_raw_error kn args ++ fnl() ++
    hov 2 (str "Custom Ltac2 printer failed:" ++ spc() ++ ppe)

let () = register_handler begin function
| Tac2interp.LtacError (kn, args) -> Some (print_error kn args)
| _ -> None
end

let () = CErrors.register_additional_error_info begin fun info ->
  if !Tac2bt.print_ltac2_backtrace then
    let bt = Exninfo.get info Tac2bt.backtrace in
    match bt with
    | None -> None
    | Some bt ->
      let bt = List.rev bt in
      let bt =
        str "Backtrace:" ++ fnl () ++ prlist_with_sep fnl pr_frame bt ++ fnl ()
      in
      Some bt
  else None
end

(** Printing *)

let print_constant ~print_def qid ?info data =
  let e = data.Tac2env.gdata_expr in
  let (_, t) = data.Tac2env.gdata_type in
  let ismut = if data.gdata_mutable then spc() ++ str "(* mutable *)" else mt() in
  let history = if not print_def then mt()
    else match data.gdata_mutation_history with
      | [] -> mt ()
      | mods ->
        let pr_one mp =
          let qid = try Nametab.shortest_qualid_of_module mp
            with Not_found ->
            try Nametab.shortest_qualid_of_dir (DirOpenModule mp)
            with Not_found -> Nametab.shortest_qualid_of_dir (DirOpenModtype mp)
          in
          pr_qualid qid
        in
        let redef = prlist_with_sep fnl pr_one mods in
        fnl () ++ str "Redefined by:" ++ fnl () ++ redef
  in
  let name = int_name () in
  let def = if print_def then
      fnl () ++ hov 2
        (pr_qualid qid ++ spc () ++ str ":=" ++ spc () ++ pr_glbexpr ~avoid:Id.Set.empty e)
    else mt()
  in
  let info = match info with
    | None -> mt()
    | Some info -> fnl() ++ fnl() ++ hov 2 (str "Compiled as" ++ spc() ++ str info.Tac2env.source)
  in
  hov 0 (
    hov 2 (pr_qualid qid ++ spc () ++ str ":" ++ spc () ++ pr_glbtype name t ++ ismut) ++ def ++ info ++ history
  )

let print_type ~print_def qid kn =
  let nparams, data = Tac2env.interp_type kn in
  let name = int_name () in
  let params = List.init nparams (fun i -> GTypVar i) in
  let ty = match params with
    | [] -> pr_qualid qid
    | [t] -> pr_glbtype name t ++ spc() ++ pr_qualid qid
    | _ -> surround (prlist_with_sep pr_comma (pr_glbtype name) params) ++ spc() ++ pr_qualid qid
  in
  let def = if not print_def || (match data with GTydDef None -> true | _ -> false)
    then mt()
    else spc() ++ str ":= " ++ match data with
      | GTydDef None -> assert false
      | GTydDef (Some t) -> pr_glbtype name t
      | GTydAlg { galg_constructors = [] } -> str "[ ]"
      | GTydAlg { galg_constructors = ctors } ->
        let pr_ctor (_, id, argtys) =
          (* XXX print warning atrtribute? *)
          hov 0
            (Id.print id ++ if CList.is_empty argtys then mt()
             else spc() ++surround (prlist_with_sep pr_comma (pr_glbtype name) argtys))
        in
        hv 0 (str "[ " ++ prlist_with_sep (fun () -> spc() ++ str "| ") pr_ctor ctors ++ str " ]")
      | GTydRec fields ->
        let pr_field (id, ismut, t) =
          hov 0 ((if ismut then str "mutable " else mt()) ++ Id.print id
                 ++ spc() ++ str ": " ++ pr_glbtype name t) ++ str ";"
        in
        hv 2 (str "{ " ++ prlist_with_sep spc pr_field fields ++ str " }")
      | GTydOpn ->
        let ctors = KerName.Map.bindings (Tac2env.find_all_constructors_in_type kn) in
        if CList.is_empty ctors then str "[ .. ]"
        else
          let pr_ctor (ckn, cdata) =
            let argtys = cdata.Tac2env.cdata_args in
            hov 0
              (Tac2print.pr_constructor ckn ++ if CList.is_empty argtys then mt()
               else spc() ++surround (prlist_with_sep pr_comma (pr_glbtype name) argtys))
          in
          hov 0 (str "[ .." ++ spc() ++ str "| "
                 ++ prlist_with_sep (fun () -> spc() ++ str "| ") pr_ctor ctors
                   ++ str " ]")
  in
  hov 2 (ty ++ def)

let print_tacref ~print_def qid = function
  | TacConstant kn ->
    let data = Tac2env.interp_global kn in
    let info = Option.map fst (Tac2env.get_compiled_global kn) in
    print_constant ~print_def qid data ?info
  | TacAlias kn ->
    let { Tac2env.alias_body = body } = Tac2env.interp_alias kn in
    str "Notation" ++ spc() ++ pr_qualid qid ++ str " :=" ++ spc()
    ++ Tac2print.pr_rawexpr_gen E5 ~avoid:Id.Set.empty body

let print_constructor qid kn =
  let cdata = Tac2env.interp_constructor kn in
  let name = int_name () in
  let ty = GTypRef (Other cdata.cdata_type, List.init cdata.cdata_prms (fun i -> GTypVar i)) in
  let ty = List.fold_right (fun arg ty -> GTypArrow (arg,ty)) cdata.cdata_args ty in
  pr_qualid qid ++ spc() ++ str ": " ++ Tac2print.pr_glbtype name ty

let locatable_ltac2 = "Ltac2"

type ltac2_object =
  | Type of type_constant
  | Constructor of ltac_constructor
  | TacRef of tacref

let locate_object qid =
  try Type (Tac2env.locate_type qid)
  with Not_found ->
  try Constructor (Tac2env.locate_constructor qid)
  with Not_found ->
  TacRef (Tac2env.locate_ltac qid)

let locate_all_object qid =
  let open Tac2env in
  (List.map (fun x -> Type x) (locate_extended_all_type qid))
  @ (List.map (fun x -> Constructor x) (locate_extended_all_constructor qid))
  @ (List.map (fun x -> TacRef x) (locate_extended_all_ltac qid))

let shortest_qualid_of_object = function
  | Type kn -> Tac2env.shortest_qualid_of_type kn
  | Constructor kn -> Tac2env.shortest_qualid_of_constructor kn
  | TacRef kn -> Tac2env.shortest_qualid_of_ltac Id.Set.empty kn

let path_of_object = function
  | Type kn -> Tac2env.path_of_type kn
  | Constructor kn -> Tac2env.path_of_constructor kn
  | TacRef kn -> Tac2env.path_of_ltac kn

let print_object ~print_def qid = function
  | Type kn -> str "Ltac2 Type" ++ spc() ++ print_type ~print_def qid kn
  | Constructor kn -> str "Ltac2 constructor" ++ spc() ++ print_constructor qid kn
  | TacRef kn -> str "Ltac2 " ++ print_tacref ~print_def qid kn

let () =
  let open Prettyp in
  let locate qid = try Some (qid, locate_object qid) with Not_found -> None in
  let locate_all qid = List.map (fun x -> qid, x) (locate_all_object qid) in
  let shortest_qualid (_,kn) = shortest_qualid_of_object kn in
  let name (_,kn) =
    let hdr = match kn with
      | Type _ -> str "Ltac2 Type"
      | TacRef (TacConstant _) -> str "Ltac2"
      | TacRef (TacAlias _) -> str "Ltac2 Notation"
      | Constructor _ -> str "Ltac2 Constructor"
    in
    hdr ++ spc () ++ pr_path (path_of_object kn)
  in
  let print (qid,kn) = print_object ~print_def:true qid kn in
  let about (qid,kn) = print_object ~print_def:false qid kn in
  register_locatable locatable_ltac2 {
    locate;
    locate_all;
    shortest_qualid;
    name;
    print;
    about;
  }

let print_located_tactic qid =
  Feedback.msg_notice (Prettyp.print_located_other (Global.env ()) locatable_ltac2 qid)

let print_ltac2 qid =
  if Tac2env.is_constructor qid then
    let kn =
      try Tac2env.locate_constructor qid
      with Not_found -> user_err ?loc:qid.CAst.loc (str "Unknown constructor " ++ pr_qualid qid)
    in
    Feedback.msg_notice (print_constructor qid kn)
  else
    let kn =
      try Tac2env.locate_ltac qid
      with Not_found -> user_err ?loc:qid.CAst.loc (str "Unknown tactic " ++ pr_qualid qid)
    in
    Feedback.msg_notice (print_tacref ~print_def:true qid kn)

let print_ltac2_type qid =
  match Tac2env.locate_type qid with
  | exception Not_found -> user_err ?loc:qid.CAst.loc (str "Unknown Ltac2 type " ++ pr_qualid qid)
  | kn ->
    Feedback.msg_notice (print_type ~print_def:true qid kn)

let print_signatures () =
  let entries = KerName.Map.bindings (Tac2env.globals ()) in
  let sort (kn1, _) (kn2, _) = KerName.compare kn1 kn2 in
  let entries = List.sort sort entries in
  let map (kn, entry) =
    let qid =
      try Some (Tac2env.shortest_qualid_of_ltac Id.Set.empty (TacConstant kn))
      with Not_found -> None
    in
    match qid with
    | None -> None
    | Some qid -> Some (qid, entry)
  in
  let entries = List.map_filter map entries in
  let pr_entry (qid, data) =
    hov 2 (print_constant ~print_def:false qid data)
  in
  Feedback.msg_notice (prlist_with_sep fnl pr_entry entries)

let typecheck_expr e =
  let e, (_,t) = Tac2intern.intern ~strict:false [] e in
  let name = int_name() in
  let pp =
    pr_glbexpr_gen E5 ~avoid:Id.Set.empty e ++ spc() ++
    str ":" ++ spc() ++ pr_glbtype name t
  in
  Feedback.msg_notice pp

let globalize_expr e =
  let avoid = Id.Set.empty in
  let e = Tac2intern.debug_globalize_allow_ext avoid e in
  Feedback.msg_notice (Tac2print.pr_rawexpr_gen E5 ~avoid e)

(** Calling tactics *)

let ltac2_interp e =
  let loc = e.loc in
  let (e, t) = intern ~strict:false [] e in
  let () = check_unit ?loc t in
  let tac = Tac2interp.interp Tac2interp.empty_environment e in
  Proofview.tclIGNORE tac

let ComTactic.Interpreter ltac2_interp = ComTactic.register_tactic_interpreter "rocq-runtime.plugins.ltac2" ltac2_interp

let call ~pstate g ~with_end_tac tac =
  let g = Option.default (Goal_select.get_default_goal_selector()) g in
  ComTactic.solve ~pstate ~with_end_tac g ~info:None (ltac2_interp tac)

let call_par ~pstate tac =
  ComTactic.solve_parallel ~pstate ~info:None (ltac2_interp tac) ~abstract:false

(** Primitive algebraic types than can't be defined Rocq-side *)

let register_prim_alg name params def =
  let id = Id.of_string name in
  let def = List.map (fun (cstr, tpe) -> (None, Id.of_string_soft cstr, tpe)) def in
  let getn (const, nonconst) (_, c, args) = match args with
  | [] -> (succ const, nonconst)
  | _ :: _ -> (const, succ nonconst)
  in
  let nconst, nnonconst = List.fold_left getn (0, 0) def in
  let alg = {
    galg_constructors = def;
    galg_nconst = nconst;
    galg_nnonconst = nnonconst;
  } in
  let def = (params, GTydAlg alg) in
  let def = { typdef_local = false; typdef_abstract = false; typdef_expr = def } in
  Lib.add_leaf (inTypDef id def)

let rocq_def n = KerName.make Tac2env.rocq_prefix (Id.of_string n)

let def_unit = {
  typdef_local = false;
  typdef_abstract = false;
  typdef_expr = 0, GTydDef (Some (GTypRef (Tuple 0, [])));
}

let t_list = rocq_def "list"

let () =
  let obj () =
     let unit = Id.of_string "unit" in
     Lib.add_leaf (inTypDef unit def_unit);
     register_prim_alg "list" 1 [
       ("[]", []);
       ("::", [GTypVar 0; GTypRef (Other t_list, [GTypVar 0])]);
     ];
  in
  Mltop.(declare_cache_obj_full (interp_only_obj obj) "rocq-runtime.plugins.ltac2")
