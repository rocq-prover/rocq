(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Pp
open Names
open Genarg
open Tac2ffi
open Tac2env
open Tac2expr
open Tac2entries.Pltac
open Proofview.Notations

open Tac2quote.Refs

let return x = Proofview.tclUNIT x

(** ML types *)

(** Embed all Ltac2 data into Values *)
let to_lvar ist =
  let open Glob_ops in
  let lfun = Tac2interp.set_env ist Id.Map.empty in
  { empty_lvar with Ltac_pretype.ltac_genargs = lfun }

let gtypref kn = GTypRef (Other kn, [])

let of_glob_constr (c:Glob_term.glob_constr) =
  match DAst.get c with
  | GGenarg (GenArg (Glbwit tag, v)) ->
    begin match genarg_type_eq tag wit_ltac2_var_quotation with
    | Some Refl ->
      begin match (fst v) with
      | ConstrVar -> GlbTacexpr (GTacVar (snd v))
      | _ -> GlbVal c
      end
    | None -> GlbVal c
    end
  | _ -> GlbVal c

let intern_constr ist c =
  let {Genintern.ltacvars=lfun; genv=env; extra; intern_sign; strict_check} = ist in
  let scope = Pretyping.WithoutTypeConstraint in
  let ltacvars = {
    Constrintern.ltac_vars = lfun;
    ltac_bound = Id.Set.empty;
    ltac_extra = extra;
  } in
  let c' = Constrintern.intern_core scope ~strict_check ~ltacvars env (Evd.from_env env) intern_sign c in
  c'

let intern_constr_tacexpr ist c =
  let c = intern_constr ist c in
  let v = of_glob_constr c in
  (v, gtypref t_constr)

let interp_constr flags ist c =
  let open Pretyping in
  let ist = to_lvar ist in
  Tac2core.pf_apply ~catch_exceptions:true begin fun env sigma ->
    let (sigma, c) = understand_ltac flags env sigma ist WithoutTypeConstraint c in
    let c = Tac2ffi.of_constr c in
    Proofview.Unsafe.tclEVARS sigma >>= fun () ->
    Proofview.tclUNIT c
  end

let () =
  let intern = intern_constr_tacexpr in
  let interp ist c = interp_constr Tac2core.constr_flags ist c in
  let print env sigma c = str "constr:(" ++ Printer.pr_lglob_constr_env env sigma c ++ str ")" in
  let raw_print env sigma c =
    str "constr:(" ++ Ppconstr.(pr_lconstr_expr ~flags:(current_flags())) env sigma c ++ str ")"
  in
  let subst subst c = Detyping.subst_glob_constr (Global.env()) subst c in
  let obj = {
    ml_intern = intern;
    ml_subst = subst;
    ml_interp = interp;
    ml_print = print;
    ml_raw_print = raw_print;
  } in
  define_ml_object Tac2quote.wit_constr obj

let () =
  let intern = intern_constr_tacexpr in
  let interp ist c = interp_constr Tac2core.open_constr_no_classes_flags ist c in
  let print env sigma c = str "open_constr:(" ++ Printer.pr_lglob_constr_env env sigma c ++ str ")" in
  let raw_print env sigma c =
    str "open_constr:(" ++ Ppconstr.(pr_lconstr_expr ~flags:(current_flags())) env sigma c ++ str ")"
  in
  let subst subst c = Detyping.subst_glob_constr (Global.env()) subst c in
  let obj = {
    ml_intern = intern;
    ml_subst = subst;
    ml_interp = interp;
    ml_print = print;
    ml_raw_print = raw_print;
  } in
  define_ml_object Tac2quote.wit_open_constr obj

let () =
  let interp _ id = return (Tac2ffi.of_ident id) in
  let print _ _ id = str "ident:(" ++ Id.print id ++ str ")" in
  let obj = {
    ml_intern = (fun _ id -> GlbVal id, gtypref t_ident);
    ml_interp = interp;
    ml_subst = (fun _ id -> id);
    ml_print = print;
    ml_raw_print = print;
  } in
  define_ml_object Tac2quote.wit_ident obj

let () =
  let intern {Genintern.ltacvars=lfun; genv=env; extra; intern_sign=_; strict_check} c =
    let sigma = Evd.from_env env in
    let ltacvars = {
      Constrintern.ltac_vars = lfun;
      ltac_bound = Id.Set.empty;
      ltac_extra = extra;
    }
    in
    let _, pat = Constrintern.intern_constr_pattern env sigma ~strict_check ~as_type:false ~ltacvars c in
    GlbVal pat, gtypref t_pattern
  in
  let subst subst c =
    let env = Global.env () in
    let sigma = Evd.from_env env in
    Patternops.subst_uninstantiated_pattern env sigma subst c
  in
  let print env sigma pat = str "pat:(" ++ Printer.pr_uninstantiated_lconstr_pattern_env env sigma pat ++ str ")" in
  let raw_print env sigma pat =
    str "pat:(" ++ Ppconstr.(pr_lconstr_pattern_expr ~flags:(current_flags())) env sigma pat ++ str ")"
  in
  let interp env c =
    let ist = to_lvar env in
    Tac2core.pf_apply ~catch_exceptions:true begin fun env sigma ->
      let c = Patternops.interp_pattern env sigma ist c in
      return (Tac2ffi.of_pattern c)
    end
  in
  let obj = {
    ml_intern = intern;
    ml_interp = interp;
    ml_subst = subst;
    ml_print = print;
    ml_raw_print = raw_print;
  } in
  define_ml_object Tac2quote.wit_pattern obj

let () =
  let intern ist c =
    let c = intern_constr ist c in
    (GlbVal (Id.Set.empty,c), gtypref t_preterm)
  in
  let interp env (ids,c) =
    let open Ltac_pretype in
    let get_preterm id = match Id.Map.find_opt id env.env_ist with
      | Some v -> to_preterm v
      | None -> assert false
    in
    let closure = {
      idents = Id.Map.empty;
      typed = Id.Map.empty;
      untyped = Id.Map.bind get_preterm ids;
      genargs = Tac2interp.set_env env Id.Map.empty;
    } in
    let c = { closure; term = c } in
    return (Tac2ffi.of_preterm c)
  in
  let subst subst (ids,c) = ids, Detyping.subst_glob_constr (Global.env()) subst c in
  let print env sigma (ids,c) =
    let ppids = if Id.Set.is_empty ids then mt()
      else prlist_with_sep spc Id.print (Id.Set.elements ids) ++ spc() ++ str "|-" ++ spc()
    in
    hov 2 (str "preterm:(" ++ ppids ++ Printer.pr_lglob_constr_env env sigma c ++ str ")")
  in
  let raw_print env sigma c =
    str "preterm:(" ++ Ppconstr.(pr_lconstr_expr ~flags:(current_flags())) env sigma c ++ str ")"
  in
  let obj = {
    ml_intern = intern;
    ml_interp = interp;
    ml_subst = subst;
    ml_print = print;
    ml_raw_print = raw_print;
  } in
  define_ml_object Tac2quote.wit_preterm obj

let () =
  let intern ist ref = match ref.CAst.v with
  | Tac2qexpr.QHypothesis id ->
    GlbVal (GlobRef.VarRef id), gtypref t_reference
  | Tac2qexpr.QReference qid ->
    let gr =
      try Smartlocate.locate_global_with_alias qid
      with Not_found as exn ->
        let _, info = Exninfo.capture exn in
        Nametab.error_global_not_found ~info qid
    in
    GlbVal gr, gtypref t_reference
  in
  let subst s c = Globnames.subst_global_reference s c in
  let interp _ gr = return (Tac2ffi.of_reference gr) in
  let print _ _ = function
  | GlobRef.VarRef id -> str "reference:(" ++ str "&" ++ Id.print id ++ str ")"
  | r -> str "reference:(" ++ Printer.pr_global r ++ str ")"
  in
  let raw_print _ _ r = match r.CAst.v with
    | Tac2qexpr.QReference qid -> str "reference:(" ++ Libnames.pr_qualid qid ++ str ")"
    | Tac2qexpr.QHypothesis id -> str "reference:(&" ++ Id.print id ++ str ")"
  in
  let obj = {
    ml_intern = intern;
    ml_subst = subst;
    ml_interp = interp;
    ml_print = print;
    ml_raw_print = raw_print;
  } in
  define_ml_object Tac2quote.wit_reference obj

(** Ltac2 in terms *)

let () =
  let interp ?loc ~poly env sigma tycon (ids, tac) =
    (* Syntax prevents bound notation variables in constr quotations *)
    let ist = Tac2interp.get_env @@ GlobEnv.lfun env in
    let () = assert (Id.Set.subset ids (Id.Map.domain ist.env_ist)) in
    let tac = Proofview.tclIGNORE (Tac2interp.interp ist tac) in
    let name, poly = Id.of_string "ltac2", poly in
    let sigma, concl = match tycon with
    | Some ty -> sigma, ty
    | None -> GlobEnv.new_type_evar env sigma ~src:(loc,Evar_kinds.InternalHole)
    in
    let c, sigma = Proof.refine_by_tactic ~name ~poly (GlobEnv.renamed_env env) sigma concl tac in
    let j = { Environ.uj_val = c; Environ.uj_type = concl } in
    (j, sigma)
  in
  GlobEnv.register_constr_interp0 wit_ltac2_constr interp

let check_judge ?loc env sigma tycon j =
  match tycon with
  | None ->
    j, sigma
  | Some ty ->
    let sigma =
      try Evarconv.unify_leq_delay env sigma j.Environ.uj_type ty
      with Evarconv.UnableToUnify (sigma,e) ->
        Pretype_errors.error_actual_type ?loc env sigma j ty e
    in
    {j with Environ.uj_type = ty}, sigma

let interp_constr_var_as_constr ?loc env sigma tycon id =
  let ist = Tac2interp.get_env @@ GlobEnv.lfun env in
  let env = GlobEnv.renamed_env env in
  let c = Id.Map.find id ist.env_ist in
  let c = Tac2ffi.to_constr c in
  let t = Retyping.get_type_of env sigma c in
  let j = { Environ.uj_val = c; uj_type = t } in
  check_judge ?loc env sigma tycon j

let interp_preterm_var_as_constr ?loc env sigma tycon id =
  let open Ltac_pretype in
  let ist = Tac2interp.get_env @@ GlobEnv.lfun env in
  let env = GlobEnv.renamed_env env in
  let c = Id.Map.find id ist.env_ist in
  let {closure; term} = Tac2ffi.to_preterm c in
  let vars = {
    ltac_constrs = closure.typed;
    ltac_uconstrs = closure.untyped;
    ltac_idents = closure.idents;
    ltac_genargs = closure.genargs;
  }
  in
  let flags = Tac2core.preterm_flags in
  let tycon = let open Pretyping in match tycon with
    | Some ty -> OfType ty
    | None -> WithoutTypeConstraint
  in
  let sigma, t, ty = Pretyping.understand_ltac_ty flags env sigma vars tycon term in
  Environ.make_judge t ty, sigma

exception NotFoundHypVar of Id.t * Id.t

let () = CErrors.register_handler @@ function
  | NotFoundHypVar (id0,id) ->
    Some
      Pp.(fmt "Hypothesis %t (value of ltac2 variable %t) not found."
            (fun () -> quote (Id.print id))
            (fun () -> quote (Id.print id0)))
  | _ -> None

let interp_hyp_var_as_constr ?loc globenv sigma tycon id0 =
  let ist = Tac2interp.get_env @@ GlobEnv.lfun globenv in
  let env = GlobEnv.renamed_env globenv in
  let v = Id.Map.find id0 ist.env_ist in
  let id = Tac2ffi.to_ident v in
  let c = try GlobEnv.lookup_renamed globenv id
    with Not_found ->
      Loc.raise ?loc (NotFoundHypVar (id0,id))
  in
  let j = Retyping.get_judgment_of env sigma c in
  check_judge ?loc env sigma tycon j

let () =
  let interp ?loc ~poly env sigma tycon (kind,id) =
    let f = match kind with
      | ConstrVar -> interp_constr_var_as_constr
      | PretermVar -> interp_preterm_var_as_constr
      | HypVar -> interp_hyp_var_as_constr
      | PatternVar -> assert false
    in
    f ?loc env sigma tycon id
  in
  GlobEnv.register_constr_interp0 wit_ltac2_var_quotation interp

let () =
  let interp _ist tac =
    (* XXX should we be doing something with the ist? *)
    let tac = Tac2interp.(interp empty_environment) tac in
    Proofview.tclBIND tac (fun _ ->
        Ftactic.return (Geninterp.Val.inject (Geninterp.val_tag (topwit Stdarg.wit_unit)) ()))
  in
  Geninterp.register_interp0 wit_ltac2_tac interp

let () =
  let interp env sigma ist (kind,id) =
    let () = match kind with
      | ConstrVar -> assert false (* checked at intern time *)
      | PretermVar -> assert false
      | HypVar -> assert false
      | PatternVar -> ()
    in
    let ist = Tac2interp.get_env ist.Ltac_pretype.ltac_genargs in
    let c = Id.Map.find id ist.env_ist in
    let c = Tac2ffi.to_pattern c in
    c
  in
  Patternops.register_interp_pat wit_ltac2_var_quotation interp

let () =
  let pr_raw (kind,id) = Genprint.PrinterBasic (fun _env _sigma ->
      let ppkind =
      match kind with
        | None -> mt()
        | Some kind -> Id.print kind.CAst.v ++ str ":"
      in
      str "$" ++ ppkind ++ Id.print id.CAst.v)
  in
  let pr_glb (kind,id) = Genprint.PrinterBasic (fun _env _sigma ->
      let ppkind = match kind with
        | ConstrVar -> mt()
        | PretermVar -> str "preterm:"
        | PatternVar -> str "pattern:"
        | HypVar -> str "hyp:"
      in
      str "$" ++ ppkind ++ Id.print id) in
  Genprint.register_noval_print0 wit_ltac2_var_quotation pr_raw pr_glb

let () =
  let subs ntnvars globs (ids, tac as orig) =
    if Id.Set.is_empty ids then
      (* closed tactic *)
      orig
    else
      (* Let-bind the notation terms inside the tactic *)
      let fold id (used_ntnvars, accu) =
        let used, c = Genintern.with_used_ntnvars ntnvars (fun () -> globs id) in
        match c with
        | None ->
          CErrors.user_err Pp.(str "Notation variable " ++ Id.print id ++ str " cannot be used in ltac2.")
        | Some c ->
          let c = GTacExt (Tac2quote.wit_preterm, (used, c)) in
          Id.Set.union used_ntnvars used, (Name id, c) :: accu
      in
      let used, bnd = Id.Set.fold fold ids (Id.Set.empty, []) in
      let tac = if List.is_empty bnd then tac else GTacLet (false, bnd, tac) in
      (used, tac)
  in
  Genintern.register_ntn_subst0 wit_ltac2_constr subs

let () =
  let pr_raw e = Genprint.PrinterBasic (fun _env _sigma ->
      let avoid = Id.Set.empty in
      (* FIXME avoid set, same as pr_glb *)
      let e = Tac2intern.debug_globalize_allow_ext avoid e in
      Tac2print.pr_rawexpr_gen ~avoid E5 e) in
  let pr_glb (ids, e) =
    let ids =
      let ids = Id.Set.elements ids in
      if List.is_empty ids then mt ()
      else hov 0 (pr_sequence Id.print ids ++ str " |-") ++ spc()
    in
    (* FIXME avoid set
       eg "Ltac2 bla foo := constr:(ltac2:(foo X.foo))"
       gets incorrectly printed as "fun foo => constr:(ltac2:(foo foo))"
       NB: can't pass through evar map store as the evar map we get is a dummy,
       see Ppconstr.pr_genarg
    *)
    Genprint.PrinterBasic Pp.(fun _env _sigma -> ids ++ Tac2print.pr_glbexpr ~avoid:Id.Set.empty e)
  in
  Genprint.register_noval_print0 wit_ltac2_constr pr_raw pr_glb

let () =
  let pr_raw e = Genprint.PrinterBasic (fun _ _ ->
      let e = Tac2intern.debug_globalize_allow_ext Id.Set.empty e in
      Tac2print.pr_rawexpr_gen ~avoid:Id.Set.empty E5 e)
  in
  let pr_glb e = Genprint.PrinterBasic (fun _ _ -> Tac2print.pr_glbexpr ~avoid:Id.Set.empty e) in
  let pr_top () = assert false in
  Genprint.register_print0 wit_ltac2_tac pr_raw pr_glb pr_top

(** Built-in notation entries *)

let add_syntax_class_full s f =
  Tac2entries.register_syntax_class (Id.of_string s) f

let add_syntax_class s intern f =
  add_syntax_class_full s {
    intern_synclass = (fun s -> Tac2entries.no_used_levels, intern s);
    interp_synclass = (fun s -> f s);
  }

let syntax_class_fail s args =
  let args = str "(" ++ prlist_with_sep (fun () -> str ", ") Tac2print.pr_syntax_class args ++ str ")" in
  CErrors.user_err (str "Invalid arguments " ++ args ++ str " in syntactic class " ++ str s)

let q_unit = CAst.make @@ CTacCst (AbsKn (Tuple 0))

let add_expr_syntax_class name entry f =
  add_syntax_class name begin function
  | [] -> ()
  | arg -> syntax_class_fail name arg
  end begin fun () ->
    Tac2entries.SyntaxRule (Procq.Symbol.nterm entry, f)
  end

let add_generic_syntax_class s entry arg =
  add_expr_syntax_class s entry (fun x -> CAst.make @@ CTacExt (arg, x))

open CAst

let () = add_syntax_class "keyword" begin function
| [SexprStr {loc;v=s}] -> s
| arg -> syntax_class_fail "keyword" arg
  end begin fun s ->
    let syntax_class = Procq.Symbol.token (Tok.PKEYWORD s) in
    Tac2entries.SyntaxRule (syntax_class, (fun _ -> q_unit))
  end

let () = add_syntax_class "terminal" begin function
| [SexprStr {loc;v=s}] -> s
| arg -> syntax_class_fail "terminal" arg
  end begin fun s ->
    let syntax_class = Procq.Symbol.token (CLexer.terminal s) in
    Tac2entries.SyntaxRule (syntax_class, (fun _ -> q_unit))
  end

let () = add_syntax_class_full "list0" {
  intern_synclass = begin function
  | [tok] ->
    let used, subclass = Tac2entries.intern_syntax_class tok in
    used, (subclass, None)
  | [tok; SexprStr {v=str}] ->
    let used, subclass = Tac2entries.intern_syntax_class tok in
    used, (subclass, Some str)
  | arg -> syntax_class_fail "list0" arg
  end;
  interp_synclass = begin function
  | subclass, None ->
    let Tac2entries.SyntaxRule (syntax_class, act) = Tac2entries.interp_syntax_class subclass in
    let syntax_class = Procq.Symbol.list0 syntax_class in
    let act l = Tac2quote.of_list act l in
    Tac2entries.SyntaxRule (syntax_class, act)
  | subclass, Some str ->
    let Tac2entries.SyntaxRule (syntax_class, act) = Tac2entries.interp_syntax_class subclass in
    let sep = Procq.Symbol.tokens [Procq.TPattern (CLexer.terminal str)] in
    let syntax_class = Procq.Symbol.list0sep syntax_class sep in
    let act l = Tac2quote.of_list act l in
    Tac2entries.SyntaxRule (syntax_class, act)
  end;
}

let () = add_syntax_class_full "list1" {
  intern_synclass = begin function
  | [tok] ->
    let used, subclass = Tac2entries.intern_syntax_class tok in
    used, (subclass, None)
  | [tok; SexprStr {v=str}] ->
    let used, subclass = Tac2entries.intern_syntax_class tok in
    used, (subclass, Some str)
  | arg -> syntax_class_fail "list1" arg
  end;
  interp_synclass = begin function
  | subclass, None ->
    let Tac2entries.SyntaxRule (syntax_class, act) = Tac2entries.interp_syntax_class subclass in
    let syntax_class = Procq.Symbol.list1 syntax_class in
    let act l = Tac2quote.of_list act l in
    Tac2entries.SyntaxRule (syntax_class, act)
  | subclass, Some str ->
    let Tac2entries.SyntaxRule (syntax_class, act) = Tac2entries.interp_syntax_class subclass in
    let sep = Procq.Symbol.tokens [Procq.TPattern (CLexer.terminal str)] in
    let syntax_class = Procq.Symbol.list1sep syntax_class sep in
    let act l = Tac2quote.of_list act l in
    Tac2entries.SyntaxRule (syntax_class, act)
  end;
}

let () = add_syntax_class_full "opt" {
  intern_synclass = begin function
  | [tok] ->
    let used, subclass = Tac2entries.intern_syntax_class tok in
    used, subclass
  | arg -> syntax_class_fail "opt" arg
  end;
  interp_synclass = begin fun subclass ->
    let Tac2entries.SyntaxRule (syntax_class, act) = Tac2entries.interp_syntax_class subclass in
    let syntax_class = Procq.Symbol.opt syntax_class in
    let act opt = match opt with
      | None ->
        CAst.make @@ CTacCst (AbsKn (Other c_none))
      | Some x ->
        CAst.make @@ CTacApp (CAst.make @@ CTacCst (AbsKn (Other c_some)), [act x])
    in
    Tac2entries.SyntaxRule (syntax_class, act)
  end;
}

let () = add_syntax_class "self" begin function
  | [] -> ()
  | arg -> syntax_class_fail "self" arg
  end begin fun () ->
    let syntax_class = Procq.Symbol.self in
    let act tac = tac in
    Tac2entries.SyntaxRule (syntax_class, act)
  end

let () = add_syntax_class "next" begin function
  | [] -> ()
  | arg -> syntax_class_fail "next" arg
  end begin fun () ->
    let syntax_class = Procq.Symbol.next in
    let act tac = tac in
    Tac2entries.SyntaxRule (syntax_class, act)
  end

let () = add_syntax_class "tactic" begin function
  | [] ->
    (* Default to level 5 parsing *)
    5
  | [SexprInt {loc;v=n}] as arg ->
    let () = if n < 0 || n > 6 then syntax_class_fail "tactic" arg in
    n
  | arg -> syntax_class_fail "tactic" arg
  end begin fun lev ->
    let syntax_class = Procq.Symbol.nterml ltac2_expr (string_of_int lev) in
    let act tac = tac in
    Tac2entries.SyntaxRule (syntax_class, act)
  end

let () = add_syntax_class_full "thunk" {
  intern_synclass = begin function
  | [tok] ->
    let used, subclass = Tac2entries.intern_syntax_class tok in
    used, subclass
  | arg -> syntax_class_fail "thunk" arg
  end;
  interp_synclass = begin fun subclass ->
    let Tac2entries.SyntaxRule (syntax_class, act) = Tac2entries.interp_syntax_class subclass in
    let act e = Tac2quote.thunk (act e) in
    Tac2entries.SyntaxRule (syntax_class, act)
  end;
}

let warn_unqualified_delimiters =
  let w = CWarnings.create_warning ~name:"deprecated-ltac2-unqualified-delimiters"
      ~from:[CWarnings.CoreCategories.ltac2; Deprecation.Version.v9_2]
      ()
  in
  CWarnings.create_in w
    Pp.(fun (s,delims) ->
        let delims () = prlist_with_sep pr_comma Id.print @@ List.rev delims in
        fmt "Delimiter arguments to %s must be qualified using \"delimiters\"@
(e.g. \"%s(delimiters(%t))\")@ unless there is a unique delimiter argument." s s delims)

let delimiters_qid = Libnames.qualid_of_string "delimiters"
let level_qid = Libnames.qualid_of_string "level"
let custom_qid = Libnames.qualid_of_string "custom"

let constr_args s arg =
  let fail () = syntax_class_fail s arg in
  let extract_id = function
    | SexprRec (_, { v = Some qid }, []) when Libnames.qualid_is_ident qid ->
      Some (Libnames.qualid_basename qid)
    | _ -> None
  in
  let force_id arg = match extract_id arg with
    | Some id -> id
    | None -> fail ()
  in
  let lev, custom, raw_delims, all_delims =
    List.fold_left (fun (lev,custom,raw_delims,all_delims) -> function
      | SexprRec (_, { v = Some qid }, [])
        when Libnames.qualid_is_ident qid ->
        let id = Libnames.qualid_basename qid in
        lev, custom, id :: raw_delims, [id] :: all_delims
      | SexprRec (_, { v = Some qid }, subargs) when Libnames.qualid_eq qid delimiters_qid ->
        lev, custom, raw_delims, (List.map force_id subargs) :: all_delims
      | SexprRec (_, { v = Some qid }, [SexprInt lev'])
        when Libnames.qualid_eq qid level_qid ->
        if Option.has_some lev then fail()
        else Some lev', custom, raw_delims, all_delims
      | SexprRec (_, { v = Some qid }, [SexprRec (_, { v = Some custom' }, [])])
        when Libnames.qualid_eq qid custom_qid ->
        if Option.has_some custom then fail()
        else lev, Some custom', raw_delims, all_delims
      | _ -> fail())
    (None,None,[],[])
    arg
  in
  let all_delims = List.concat (List.rev all_delims) in
  let () = match raw_delims, arg with
    | [], _ -> ()
    | [delim], [arg] when Option.equal Id.equal (Some delim) (extract_id arg) -> ()
    | _ -> warn_unqualified_delimiters (s,raw_delims)
  in
  lev, custom, List.rev all_delims

let constr_delimiters s arg =
  let lev, custom, scopes = constr_args s arg in
  let () = if Option.has_some lev then
      CErrors.user_err Pp.(str "Specifying level not allowed for syntax class " ++ str s ++ str ".")
  in
  let () = if Option.has_some custom then
      CErrors.user_err Pp.(str "Custom entry not allowed for syntax class " ++ str s ++ str ".")
  in
  scopes

let constr_args s arg =
  let lev, custom, scopes = constr_args s arg in
  let custom = custom
    |> Option.map (fun custom ->
        try Nametab.CustomEntries.locate custom
        with Not_found -> CErrors.user_err ?loc:custom.loc Pp.(str "Unknown custom entry " ++ Libnames.pr_qualid custom ++ str "."))
  in
  let () = lev |> Option.iter (fun lev -> if lev.v < 0 then CErrors.user_err ?loc:lev.loc Pp.(str "Level must be nonnegative.")) in
  let lev = lev |> Option.map (fun lev -> string_of_int lev.v) in
  (lev, custom), scopes

let constr_symb (lev,custom) =
  let custom = Option.map (fun custom -> fst @@ Egramrocq.find_custom_entry custom) custom in
  match lev, custom with
  | None, None -> Procq.Symbol.nterm Procq.Constr.constr
  | Some lev, None -> Procq.Symbol.nterml Procq.Constr.term lev
  | None, Some custom -> Procq.Symbol.nterm custom
  | Some lev, Some custom ->
    Procq.Symbol.nterml custom lev

let add_constr_classes (name,lname) quote =
  let () =
    let s = name in
    add_syntax_class s (constr_args s) begin function (symb,delimiters) ->
      let act e = quote ?delimiters:(Some delimiters) e in
      Tac2entries.SyntaxRule (constr_symb symb, act)
    end
  in
  let () =
    let s = lname in
    add_syntax_class s (constr_delimiters s) begin function delimiters ->
      let act e = quote ?delimiters:(Some delimiters) e in
      Tac2entries.SyntaxRule (Procq.Symbol.nterm Procq.Constr.lconstr, act)
    end
  in
  ()

let () = add_constr_classes ("constr","lconstr") Tac2quote.of_constr

let () = add_constr_classes ("open_constr","open_lconstr") Tac2quote.of_open_constr

let () = add_constr_classes ("preterm","lpreterm") Tac2quote.of_preterm

let () = add_expr_syntax_class "ident" q_ident (fun id -> Tac2quote.of_anti Tac2quote.of_ident id)
let () = add_expr_syntax_class "bindings" q_bindings Tac2quote.of_bindings
let () = add_expr_syntax_class "with_bindings" q_with_bindings Tac2quote.of_bindings
let () = add_expr_syntax_class "intropattern" q_intropattern Tac2quote.of_intro_pattern
let () = add_expr_syntax_class "intropatterns" q_intropatterns Tac2quote.of_intro_patterns
let () = add_expr_syntax_class "destruction_arg" q_destruction_arg Tac2quote.of_destruction_arg
let () = add_expr_syntax_class "induction_clause" q_induction_clause Tac2quote.of_induction_clause
let () = add_expr_syntax_class "conversion" q_conversion Tac2quote.of_conversion
let () = add_expr_syntax_class "orient" q_orient Tac2quote.of_orient
let () = add_expr_syntax_class "rewriting" q_rewriting Tac2quote.of_rewriting
let () = add_expr_syntax_class "clause" q_clause Tac2quote.of_clause
let () = add_expr_syntax_class "hintdb" q_hintdb Tac2quote.of_hintdb
let () = add_expr_syntax_class "occurrences" q_occurrences Tac2quote.of_occurrences
let () = add_expr_syntax_class "dispatch" q_dispatch Tac2quote.of_dispatch
let () = add_expr_syntax_class "strategy" q_strategy_flag Tac2quote.of_strategy_flag
let () = add_expr_syntax_class "reference" q_reference Tac2quote.of_reference
let () = add_expr_syntax_class "move_location" q_move_location Tac2quote.of_move_location
let () = add_expr_syntax_class "pose" q_pose Tac2quote.of_pose
let () = add_expr_syntax_class "assert" q_assert Tac2quote.of_assertion
let () = add_expr_syntax_class "constr_matching" q_constr_matching Tac2quote.of_constr_matching
let () = add_expr_syntax_class "goal_matching" q_goal_matching Tac2quote.of_goal_matching
let () = add_expr_syntax_class "format" Procq.Prim.lstring Tac2quote.of_format

let () = add_generic_syntax_class "pattern" Procq.Constr.constr Tac2quote.wit_pattern

(** seq syntax_class, a bit hairy *)

open Procq

type _ converter =
| CvNil : (Loc.t -> raw_tacexpr) converter
| CvCns : 'act converter * ('a -> raw_tacexpr) option -> ('a -> 'act) converter

let rec apply : type a. a converter -> raw_tacexpr list -> a = function
| CvNil -> fun accu loc -> Tac2quote.of_tuple ~loc accu
| CvCns (c, None) -> fun accu x -> apply c accu
| CvCns (c, Some f) -> fun accu x -> apply c (f x :: accu)

type seqrule =
| Seqrule : (Tac2expr.raw_tacexpr, Gramlib.Grammar.norec, 'act, Loc.t -> raw_tacexpr) Rule.t * 'act converter -> seqrule

let rec make_seq_rule = function
| [] ->
  Seqrule (Procq.Rule.stop, CvNil)
| (skip,tok) :: rem ->
  let Tac2entries.SyntaxRule (syntax_class, f) = Tac2entries.interp_syntax_class tok in
  let syntax_class =
    match Procq.generalize_symbol syntax_class with
    | None ->
      CErrors.user_err (str "Recursive symbols (self / next) are not allowed in local rules")
    | Some syntax_class -> syntax_class
  in
  let Seqrule (r, c) = make_seq_rule rem in
  let r = Procq.Rule.next_norec r syntax_class in
  let f = if skip then None else Some f in
  Seqrule (r, CvCns (c, f))

let interp_seq_rule toks =
  let Seqrule (r, c) = make_seq_rule (List.rev toks) in
  let syntax_class =
    Procq.(Symbol.rules [Rules.make r (apply c [])])
  in
  Tac2entries.SyntaxRule (syntax_class, (fun e -> e))

let intern_seq_rule toks =
  List.fold_left_map (fun used tok ->
      let used', rule = Tac2entries.intern_syntax_class tok in
      let skip = match tok with
        | SexprStr _ -> true (* Leave out mere strings *)
        | _ -> false
      in
      Tac2entries.union_used_levels used used', (skip, rule))
    Tac2entries.no_used_levels
    toks

let () = add_syntax_class_full "seq" {
  intern_synclass = intern_seq_rule;
  interp_synclass = interp_seq_rule;
}
