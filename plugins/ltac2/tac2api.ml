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
open Tac2val
open Tac2ffi
open Tac2extffi
open Tac2expr
open Tac2externals
open Tac2helpers
open Proofview.Notations

module CInt = Int

(** Standard values *)

let v_blk = Valexpr.make_block

let of_rec_declaration (nas, ts, cs) =
  let binders = Array.map2 (fun na t -> (na, t)) nas ts in
  (Tac2ffi.of_array of_binder binders,
  Tac2ffi.of_array Tac2ffi.of_constr cs)

let to_rec_declaration (nas, cs) =
  let nas = Tac2ffi.to_array to_binder nas in
  (Array.map fst nas,
  Array.map snd nas,
  Tac2ffi.to_array Tac2ffi.to_constr cs)

let of_case_invert = let open Constr in function
  | NoInvert -> ValInt 0
  | CaseInvert {indices} ->
    v_blk 0 [|of_array of_constr indices|]

let to_case_invert = let open Constr in function
  | ValInt 0 -> NoInvert
  | ValBlk (0, [|indices|]) ->
    let indices = to_array to_constr indices in
    CaseInvert {indices}
  | _ -> CErrors.anomaly Pp.(str "unexpected value shape")

(** Printing *)

module Ltac2Message = struct
  let print m = Feedback.msg_notice m

  let empty = Pp.mt ()

  let of_int = Pp.int

  let of_string = Pp.str

  let to_string = Pp.string_of_ppcmds

  let of_constr c =
    pf_apply @@ fun env sigma -> return (Printer.pr_econstr_env env sigma c)

  let of_lconstr c =
    pf_apply @@ fun env sigma -> return (Printer.pr_leconstr_env env sigma c)

  let of_preterm c =
    pf_apply @@ fun env sigma -> return (Printer.pr_closed_glob_env env sigma c)

  let of_lpreterm c =
    pf_apply @@ fun env sigma -> return (Printer.pr_closed_lglob_env env sigma c)

  let of_ident = Id.print

  let of_exn v env sigma =
    let open Tac2quote.Refs in
    Tac2print.pr_valexpr env sigma v (GTypRef (Other t_exn, []))

  let of_exninfo = CErrors.print_extra

  let concat = Pp.app

  let force_new_line = Pp.fnl ()

  let break i j = Pp.brk (i, j)

  let space = Pp.spc ()

  let hbox = Pp.h

  let vbox = Pp.v

  let hvbox = Pp.hv

  let hovbox = Pp.hov

  module Format = struct
    open Tac2types

    let stop = []

    let string s = FmtString :: s

    let int s = FmtInt :: s

    let constr s = FmtConstr :: s

    let ident s = FmtIdent :: s

    let literal l s = FmtLiteral l :: s

    let alpha s = FmtAlpha :: s

    let alpha0 s = FmtAlpha0 :: s

    let message s = FmtMessage :: s

    let arity_of_format fmt =
      let fold accu = function
        | FmtLiteral _ -> accu
        | FmtString | FmtInt | FmtConstr | FmtIdent | FmtMessage -> 1 + accu
        | FmtAlpha | FmtAlpha0 -> 2 + accu
      in
      List.fold_left fold 0 fmt

    let kfprintf k fmt =
      let pop1 l = match l with [] -> assert false | x :: l -> (x, l) in
      let pop2 l = match l with [] | [_] -> assert false | x :: y :: l -> (x, y, l) in
      let arity = arity_of_format fmt in
      let rec eval accu args fmt = match fmt with
        | [] -> apply k [of_pp accu]
        | tag :: fmt ->
           match tag with
           | FmtLiteral s ->
              eval (Pp.app accu (Pp.str s)) args fmt
           | FmtString ->
              let (s, args) = pop1 args in
              let pp = Pp.str (Tac2ffi.to_string s) in
              eval (Pp.app accu pp) args fmt
           | FmtInt ->
              let (i, args) = pop1 args in
              let pp = Pp.int (to_int i) in
              eval (Pp.app accu pp) args fmt
           | FmtConstr ->
              let (c, args) = pop1 args in
              let c = to_constr c in
              pf_apply begin fun env sigma ->
                let pp = Printer.pr_econstr_env env sigma c in
                eval (Pp.app accu pp) args fmt
                end
           | FmtIdent ->
              let (i, args) = pop1 args in
              let pp = Id.print (to_ident i) in
              eval (Pp.app accu pp) args fmt
           | FmtMessage ->
              let (m, args) = pop1 args in
              let m = to_pp m in
              eval (Pp.app accu m) args fmt
           | FmtAlpha ->
              let (f, x, args) = pop2 args in
              Tac2val.apply_val f [of_unit (); x] >>= fun pp ->
              eval (Pp.app accu (to_pp pp)) args fmt
           | FmtAlpha0 ->
              let (f, x, args) = pop2 args in
              Tac2val.apply_val f [x] >>= fun pp ->
              eval (Pp.app accu (to_pp pp)) args fmt
      in
      let eval v = eval (Pp.mt ()) v fmt in
      if Int.equal arity 0 then eval []
      else return (Tac2ffi.of_closure (Tac2val.abstract arity eval))

    let ikfprintf k v fmt =
      let arity = arity_of_format fmt in
      let eval _args = apply k [v] in
      if Int.equal arity 0 then eval []
      else return (Tac2ffi.of_closure (Tac2val.abstract arity eval))
  end
end

(** Array *)

module Ltac2Array = struct
  let empty = v_blk 0 [||]

  let make n x =
    try return (v_blk 0 (Array.make n x))
    with Invalid_argument _ -> throw Tac2ffi.err_outofbounds

  let length (_, v) = Array.length v

  let set (_, v) n x =
    try Array.set v n x; return ()
    with Invalid_argument _ -> throw Tac2ffi.err_outofbounds

  let get (_, v) n =
    try return (Array.get v n)
    with Invalid_argument _ -> throw Tac2ffi.err_outofbounds

  let lowlevel_blit (_, v0) s0 (_, v1) s1 l =
    try Array.blit v0 s0 v1 s1 l; return ()
    with Invalid_argument _ -> throw Tac2ffi.err_outofbounds

  let lowlevel_fill (_, d) s l v =
    try Array.fill d s l v; return ()
    with Invalid_argument _ -> throw Tac2ffi.err_outofbounds

  let concat l = v_blk 0 (Array.concat (List.map snd l))
end

(** Ident *)

module Ltac2Ident = struct
  type t = Id.t
  let equal = Id.equal

  let to_string = Id.to_string

  let of_string s =
    try Some (Id.of_string s)
    with e when CErrors.noncritical e -> None
end

(** Int *)

module Ltac2Int = struct
  type t = int
  let equal = (==)

  let neg = (~-)
  let abs = Stdlib.abs

  let compare = Int.compare
  let add = (+)
  let sub = (-)
  let mul = ( * )

  let div m n =
    if n == 0 then throw Tac2ffi.err_division_by_zero
    else return (m / n)
  let (mod) m n =
    if n == 0 then throw Tac2ffi.err_division_by_zero
    else return (m mod n)

  let (asr) = (asr)
  let (lsl) = (lsl)
  let (lsr) = (lsr)
  let (land) = (land)
  let (lor) = (lor)
  let (lxor) = (lxor)
  let (lnot) = (lnot)
end

(** Char *)

module Ltac2Char = struct
  type t = char
  let of_int i =
    try return (Char.chr i)
    with Invalid_argument _ as e ->
      let e, info = Exninfo.capture e in
      throw ~info e

  let to_int = Char.code
end

(** String *)

module Ltac2String = struct
  type t = Bytes.t
  let make n c =
    try return (Bytes.make n c)
    with Invalid_argument _ -> throw Tac2ffi.err_outofbounds

  let length = Bytes.length

  let set s n c =
    try Bytes.set s n c; return ()
    with Invalid_argument _ -> throw Tac2ffi.err_outofbounds

  let get s n =
    try return (Bytes.get s n)
    with Invalid_argument _ -> throw Tac2ffi.err_outofbounds

  let concat = Bytes.concat

  let app a b = Bytes.concat Bytes.empty [a; b]

  let sub s off len =
    try return (Bytes.sub s off len)
    with Invalid_argument _ -> throw Tac2ffi.err_outofbounds

  let equal = Bytes.equal

  let compare = Bytes.compare
end

(** Pstring *)

module Ltac2Pstring = struct
  type t = Pstring.t
  type char63 = Uint63.t
  let max_length = Pstring.max_length
  let to_string = Pstring.to_string
  let of_string = Pstring.of_string
  let make   = Pstring.make
  let length = Pstring.length
  let get    = Pstring.get
  let sub    = Pstring.sub
  let cat    = Pstring.cat
  let equal   = Pstring.equal
  let compare = Pstring.compare
end

(** Terms *)

module Ltac2Constr = struct
  type t = EConstr.t

  let type_ c =
    let get_type env sigma =
      let (sigma, t) = Typing.type_of env sigma c in
      let t = Tac2ffi.of_constr t in
      Proofview.Unsafe.tclEVARS sigma <*> Proofview.tclUNIT t
    in
    pf_apply ~catch_exceptions:true get_type

  let equal c1 c2 =
    Proofview.tclEVARMAP >>= fun sigma -> return (EConstr.eq_constr sigma c1 c2)

  module Unsafe = struct
    let kind c env sigma =
      let open Constr in
      match EConstr.kind sigma c with
      | Rel n ->
         v_blk 0 [|Tac2ffi.of_int n|]
      | Var id ->
         v_blk 1 [|Tac2ffi.of_ident id|]
      | Meta n ->
         v_blk 2 [|Tac2ffi.of_int n|]
      | Evar (evk, args) ->
         let args = Evd.expand_existential sigma (evk, args) in
         v_blk 3 [|
             Tac2ffi.of_evar evk;
             Tac2ffi.of_array Tac2ffi.of_constr (Array.of_list args);
           |]
      | Sort s ->
         v_blk 4 [|Tac2ffi.of_sort s|]
      | Cast (c, k, t) ->
         v_blk 5 [|
             Tac2ffi.of_constr c;
             Tac2ffi.of_cast k;
             Tac2ffi.of_constr t;
           |]
      | Prod (na, t, u) ->
         v_blk 6 [|
             of_binder (na, t);
             Tac2ffi.of_constr u;
           |]
      | Lambda (na, t, c) ->
         v_blk 7 [|
             of_binder (na, t);
             Tac2ffi.of_constr c;
           |]
      | LetIn (na, b, t, c) ->
         v_blk 8 [|
             of_binder (na, t);
             Tac2ffi.of_constr b;
             Tac2ffi.of_constr c;
           |]
      | App (c, cl) ->
         v_blk 9 [|
             Tac2ffi.of_constr c;
             Tac2ffi.of_array Tac2ffi.of_constr cl;
           |]
      | Const (cst, u) ->
         v_blk 10 [|
             Tac2ffi.of_constant cst;
             Tac2ffi.of_instance u;
           |]
      | Ind (ind, u) ->
         v_blk 11 [|
             Tac2ffi.of_inductive ind;
             Tac2ffi.of_instance u;
           |]
      | Construct (cstr, u) ->
         v_blk 12 [|
             Tac2ffi.of_constructor cstr;
             Tac2ffi.of_instance u;
           |]
      | Case (ci, u, pms, c, iv, t, bl) ->
         (* FIXME: also change representation Ltac2-side? *)
         let (ci, c, iv, t, bl) = EConstr.expand_case env sigma (ci, u, pms, c, iv, t, bl) in
         let c = on_snd (EConstr.ERelevance.kind sigma) c in
         v_blk 13 [|
             Tac2ffi.of_case ci;
             Tac2ffi.(of_pair of_constr of_relevance c);
             of_case_invert iv;
             Tac2ffi.of_constr t;
             Tac2ffi.of_array Tac2ffi.of_constr bl;
           |]
      | Fix ((recs, i), def) ->
         let (nas, cs) = of_rec_declaration def in
         v_blk 14 [|
             Tac2ffi.of_array Tac2ffi.of_int recs;
             Tac2ffi.of_int i;
             nas;
             cs;
           |]
      | CoFix (i, def) ->
         let (nas, cs) = of_rec_declaration def in
         v_blk 15 [|
             Tac2ffi.of_int i;
             nas;
             cs;
           |]
      | Proj (p, r, c) ->
         v_blk 16 [|
             Tac2ffi.of_projection p;
             Tac2ffi.of_relevance (EConstr.ERelevance.kind sigma r);
             Tac2ffi.of_constr c;
           |]
      | Int n ->
         v_blk 17 [|Tac2ffi.of_uint63 n|]
      | Float f ->
         v_blk 18 [|Tac2ffi.of_float f|]
      | String s ->
         v_blk 19 [|Tac2ffi.of_pstring s|]
      | Array(u,t,def,ty) ->
         v_blk 20 [|
             of_instance u;
             Tac2ffi.of_array Tac2ffi.of_constr t;
             Tac2ffi.of_constr def;
             Tac2ffi.of_constr ty;
           |]

    let make knd env sigma =
      match Tac2ffi.to_block knd with
      | (0, [|n|]) ->
         let n = Tac2ffi.to_int n in
         EConstr.mkRel n
      | (1, [|id|]) ->
         let id = Tac2ffi.to_ident id in
         EConstr.mkVar id
      | (2, [|n|]) ->
         let n = Tac2ffi.to_int n in
         EConstr.mkMeta n
      | (3, [|evk; args|]) ->
         let evk = to_evar evk in
         let args = Tac2ffi.to_array Tac2ffi.to_constr args in
         EConstr.mkLEvar sigma (evk, Array.to_list args)
      | (4, [|s|]) ->
         let s = Tac2ffi.to_sort s in
         EConstr.mkSort s
      | (5, [|c; k; t|]) ->
         let c = Tac2ffi.to_constr c in
         let k = Tac2ffi.to_cast k in
         let t = Tac2ffi.to_constr t in
         EConstr.mkCast (c, k, t)
      | (6, [|na; u|]) ->
         let (na, t) = to_binder na in
         let u = Tac2ffi.to_constr u in
         EConstr.mkProd (na, t, u)
      | (7, [|na; c|]) ->
         let (na, t) = to_binder na in
         let u = Tac2ffi.to_constr c in
         EConstr.mkLambda (na, t, u)
      | (8, [|na; b; c|]) ->
         let (na, t) = to_binder na in
         let b = Tac2ffi.to_constr b in
         let c = Tac2ffi.to_constr c in
         EConstr.mkLetIn (na, b, t, c)
      | (9, [|c; cl|]) ->
         let c = Tac2ffi.to_constr c in
         let cl = Tac2ffi.to_array Tac2ffi.to_constr cl in
         EConstr.mkApp (c, cl)
      | (10, [|cst; u|]) ->
         let cst = Tac2ffi.to_constant cst in
         let u = to_instance u in
         EConstr.mkConstU (cst, u)
      | (11, [|ind; u|]) ->
         let ind = Tac2ffi.to_inductive ind in
         let u = to_instance u in
         EConstr.mkIndU (ind, u)
      | (12, [|cstr; u|]) ->
         let cstr = Tac2ffi.to_constructor cstr in
         let u = to_instance u in
         EConstr.mkConstructU (cstr, u)
      | (13, [|ci; c; iv; t; bl|]) ->
         let ci = Tac2ffi.to_case ci in
         let c = Tac2ffi.(to_pair to_constr to_relevance c) in
         let c = on_snd EConstr.ERelevance.make c in
         let iv = to_case_invert iv in
         let t = Tac2ffi.to_constr t in
         let bl = Tac2ffi.to_array Tac2ffi.to_constr bl in
         EConstr.mkCase (EConstr.contract_case env sigma (ci, c, iv, t, bl))
      | (14, [|recs; i; nas; cs|]) ->
         let recs = Tac2ffi.to_array Tac2ffi.to_int recs in
         let i = Tac2ffi.to_int i in
         let def = to_rec_declaration (nas, cs) in
         EConstr.mkFix ((recs, i), def)
      | (15, [|i; nas; cs|]) ->
         let i = Tac2ffi.to_int i in
         let def = to_rec_declaration (nas, cs) in
         EConstr.mkCoFix (i, def)
      | (16, [|p; r; c|]) ->
         let p = Tac2ffi.to_projection p in
         let r = to_relevance r in
         let c = Tac2ffi.to_constr c in
         EConstr.mkProj (p, EConstr.ERelevance.make r, c)
      | (17, [|n|]) ->
         let n = Tac2ffi.to_uint63 n in
         EConstr.mkInt n
      | (18, [|f|]) ->
         let f = Tac2ffi.to_float f in
         EConstr.mkFloat f
      | (19, [|s|]) ->
         let s = Tac2ffi.to_pstring s in
         EConstr.mkString s
      | (20, [|u;t;def;ty|]) ->
         let t = Tac2ffi.to_array Tac2ffi.to_constr t in
         let def = Tac2ffi.to_constr def in
         let ty = Tac2ffi.to_constr ty in
         let u = to_instance u in
         EConstr.mkArray(u,t,def,ty)
      | _ -> assert false

    let check c =
      pf_apply @@ fun env sigma ->
                  try
                    let (sigma, _) = Typing.type_of env sigma c in
                    Proofview.Unsafe.tclEVARS sigma >>= fun () ->
                    return (Tac2ffi.of_result Tac2ffi.of_constr (Ok c))
                  with e when CErrors.noncritical e ->
                    let e = Exninfo.capture e in
                    return (Tac2ffi.of_result Tac2ffi.of_constr (Error e))

    let liftn = EConstr.Vars.liftn

    let substnl = EConstr.Vars.substnl

    let closenl ids k c =
      Proofview.tclEVARMAP >>= fun sigma ->
      return (EConstr.Vars.substn_vars sigma k ids c)

    let closednl n c =
      Proofview.tclEVARMAP >>= fun sigma ->
      return (EConstr.Vars.closedn sigma n c)

    let noccur_between n m c =
      Proofview.tclEVARMAP >>= fun sigma ->
      return (EConstr.Vars.noccur_between sigma n m c)

    let case ind =
      Proofview.tclENV >>= fun env ->
      try
        let ans = Inductiveops.make_case_info env ind Constr.MatchStyle in
        return (Tac2ffi.of_case ans)
      with e when CErrors.noncritical e ->
        throw Tac2ffi.err_notfound

    type case = Constr.case_info

    module Case = struct
      open Constr

      let equal x y = Ind.UserOrd.equal x.ci_ind y.ci_ind
      let inductive case = case.ci_ind
    end
  end

  module Binder = struct
    type t = binder
    type relevance = Sorts.relevance

    let make na ty =
      pf_apply @@ fun env sigma ->
      match Retyping.relevance_of_type env sigma ty with
      | rel ->
         let na = match na with None -> Anonymous | Some id -> Name id in
        return (Context.make_annot na rel, ty)
      | exception (Retyping.RetypeError _ as e) ->
        let e, info = Exninfo.capture e in
        fail ~info (CErrors.UserError Pp.(str "Not a type."))

    let unsafe_make na rel ty =
      let na =
        match na with
        | None -> Anonymous
        | Some id -> Name id
      in Context.make_annot na (EConstr.ERelevance.make rel), ty

    let name (bnd, _) =
      match bnd.Context.binder_name with
      | Anonymous -> None
      | Name id -> Some id

    (* type is a reserved keyword *)
    let type_ (_, ty) = ty

    let relevance (na, _) = EConstr.Unsafe.to_relevance na.Context.binder_relevance
  end

  module Cast = struct
    type t = Constr.cast_kind
    let equal = Glob_ops.cast_kind_eq

    let default = of_cast DEFAULTcast
    let vm      = of_cast VMcast
    let native  = of_cast NATIVEcast
  end

  let in_context id t c =
    Proofview.Goal.goals >>= function
    | [gl] ->
       gl >>= fun gl ->
       let env = Proofview.Goal.env gl in
       let sigma = Proofview.Goal.sigma gl in
       let has_var =
         try
           let _ = Environ.lookup_named id env in
           true
         with Not_found -> false
       in
       if has_var then
         Tacticals.tclZEROMSG (str "Variable already exists")
       else
         let open Context.Named.Declaration in
         let sigma, t_rel =
           let t_ty = Retyping.get_type_of env sigma t in
           (* If the user passed eg ['_] for the type we force it to indeed be a type *)
           let sigma, j = Typing.type_judgment env sigma {uj_val=t; uj_type=t_ty} in
           sigma, EConstr.ESorts.relevance_of_sort j.utj_type
         in
         let nenv = EConstr.push_named (LocalAssum (Context.make_annot id t_rel, t)) env in
         let (sigma, (evt, s)) = Evarutil.new_type_evar nenv sigma Evd.univ_flexible in
         let relevance = EConstr.ESorts.relevance_of_sort s in
         let (sigma, evk) = Evarutil.new_pure_evar (Environ.named_context_val nenv) sigma ~relevance evt in
         Proofview.Unsafe.tclEVARS sigma >>= fun () ->
         Proofview.Unsafe.tclSETGOALS [Proofview.with_empty_state evk] >>= fun () ->
         thaw c >>= fun _ ->
         Proofview.Unsafe.tclSETGOALS [Proofview.goal_with_state (Proofview.Goal.goal gl) (Proofview.Goal.state gl)] >>= fun () ->
         let args = EConstr.identity_subst_val (Environ.named_context_val env) in
         let args = SList.cons (EConstr.mkRel 1) args in
         let ans = EConstr.mkEvar (evk, args) in
         return (EConstr.mkLambda (Context.make_annot (Name id) t_rel, t, ans))
    | _ ->
       throw Tac2ffi.err_notfocussed

  module Pretype = struct
    open Pretyping
    type expected_type = Pretyping.typing_constraint

    module Flags = struct
      type t = Pretyping.inference_flags

      let constr_flags = {
          use_coercions = true;
          use_typeclasses = Pretyping.UseTC;
          solve_unification_constraints = true;
          fail_evar = true;
          expand_evars = true;
          program_mode = false;
          poly = PolyFlags.default;
          undeclared_evars_rr = false;
          unconstrained_sorts = false;
        }

      let set_use_coercion b (flags: t) =
        { flags with use_coercions = b }

      let set_use_typeclasses b flags =
        { flags with use_typeclasses = if b then UseTC else NoUseTC }

      let set_allow_evars b flags =
        { flags with fail_evar = not b }

      let set_nf_evars b flags =
        { flags with expand_evars = b }
    end

    let expected_istype = IsType
    let expected_oftype c = OfType c
    let expected_without_type_constraint = WithoutTypeConstraint

    let pretype flags expected_type c =
      let pretype env sigma =
        let sigma, t = Pretyping.understand_uconstr ~flags ~expected_type env sigma c in
        Proofview.Unsafe.tclEVARS sigma <*> Proofview.tclUNIT t
      in
      pf_apply ~catch_exceptions:true pretype
  end

  module Relevance = struct
    type t = Binder.relevance

    let equal r1 r2 _env sigma =
      EConstr.ERelevance.(equal sigma (make r1) (make r2))

    let relevant = Sorts.Relevant

    let irrelevant = Sorts.Irrelevant
  end

  let has_evar c =
    Proofview.tclEVARMAP >>= fun sigma ->
    return (Evarutil.has_undefined_evars sigma c)
end

(** Uint63 *)

module Ltac2Uint63 = struct
  type t = Uint63.t
  let equal = Uint63.equal
  let compare = Uint63.compare

  let of_int = Uint63.of_int

  let print i = Pp.str (Uint63.to_string i)
end

(** Evar *)

module Ltac2Evar = struct
  type t = Evar.t
  let equal = Evar.equal
end

(** Float *)

module Ltac2Float = struct
  type t = Float64.t
  let equal = Float64.equal
end

(** Meta *)

module Ltac2Meta = struct
  type t = Int.t
  let equal = Int.equal
end

(** Constant *)

module Ltac2Constant = struct
  type t = Constant.t
  let equal = Constant.UserOrd.equal

  let print c = Nametab.pr_global_env Id.Set.empty (ConstRef c)
end

(** Patterns *)

module Ltac2Pattern = struct
  type context = Constr_matching.context
  let empty_context = Constr_matching.empty_context

  let matches pat c =
    pf_apply begin fun env sigma ->
      let ans =
        try Some (Constr_matching.matches env sigma pat c)
        with Constr_matching.PatternMatchingFailure -> None
      in
      begin match ans with
      | None -> fail Tac2ffi.err_matchfailure
      | Some ans ->
         let ans = Id.Map.bindings ans in
         let of_pair (id, c) = Tac2ffi.of_tuple [| Tac2ffi.of_ident id; Tac2ffi.of_constr c |] in
         return (Tac2ffi.of_list of_pair ans)
      end
    end

  let matches_subterm pat c =
    let open Constr_matching in
    let rec of_ans s = match IStream.peek s with
      | IStream.Nil -> fail Tac2ffi.err_matchfailure
      | IStream.Cons ({ m_sub = (_, sub); m_ctx }, s) ->
         let ans = Id.Map.bindings sub in
         Proofview.tclOR (return (m_ctx, ans)) (fun _ -> of_ans s)
    in
    pf_apply begin fun env sigma ->
      let ans = Constr_matching.match_subterm env sigma (Id.Set.empty,pat) c in
      of_ans ans
    end

  let matches_vect pat c =
    pf_apply begin fun env sigma ->
      let ans =
        try Some (Constr_matching.matches env sigma pat c)
        with Constr_matching.PatternMatchingFailure -> None
      in
      match ans with
      | None -> fail Tac2ffi.err_matchfailure
      | Some ans ->
         let ans = Id.Map.bindings ans in
         let ans = Array.map_of_list snd ans in
         return (Tac2ffi.of_array Tac2ffi.of_constr ans)
    end

  let matches_subterm_vect pat c =
    let open Constr_matching in
    let rec of_ans s = match IStream.peek s with
      | IStream.Nil -> fail Tac2ffi.err_matchfailure
      | IStream.Cons ({ m_sub = (_, sub); m_ctx }, s) ->
         let ans = Id.Map.bindings sub in
         let ans = Array.map_of_list snd ans in
         Proofview.tclOR (return (m_ctx,ans)) (fun _ -> of_ans s)
    in
    pf_apply begin fun env sigma ->
      let ans = Constr_matching.match_subterm env sigma (Id.Set.empty,pat) c in
      of_ans ans
    end

  let matches_goal rev hp cp =
    assert_focussed >>= fun () ->
    Proofview.Goal.enter_one begin fun gl ->
      let env = Proofview.Goal.env gl in
      let sigma = Proofview.Goal.sigma gl in
      let concl = Proofview.Goal.concl gl in
      Tac2match.match_goal env sigma concl ~rev (hp, cp) >>= fun (hyps, ctx, subst) ->
      let empty_context = Constr_matching.empty_context in
      let of_ctxopt ctx = Tac2ffi.of_matching_context (Option.default empty_context ctx) in
      let hids = Tac2ffi.of_array Tac2ffi.of_ident (Array.map_of_list pi1 hyps) in
      let hbctx = Tac2ffi.of_array of_ctxopt
                    (Array.of_list (CList.filter_map (fun (_,bctx,_) -> bctx) hyps))
      in
      let hctx = Tac2ffi.of_array of_ctxopt (Array.map_of_list pi3 hyps) in
      let subs = Tac2ffi.of_array Tac2ffi.of_constr (Array.map_of_list snd (Id.Map.bindings subst)) in
      let cctx = of_ctxopt ctx in
      let ans = Tac2ffi.of_tuple [| hids; hbctx; hctx; subs; cctx |] in
      Proofview.tclUNIT ans
    end

  let instantiate = Constr_matching.instantiate_context
end

(** Control *)

module Ltac2Control = struct
  let zero (e, info) = fail ~info e

  let zero_bt (e, _) info = Proofview.tclZERO ~info e

  let plus x k = Proofview.tclOR (thaw x) k

  let plus_bt run handle =
    Proofview.tclOR (thaw run) (fun e -> handle e (snd e))

  let once f = Proofview.tclONCE (thaw f)

  let case f =
    Proofview.tclCASE (thaw f) >>= begin function
    | Proofview.Next (x, k) ->
      let k (e,info) = set_bt info >>= fun info -> k (e,info) in
      return (Ok (x, k))
    | Proofview.Fail e -> return (Error e)
    end

  let numgoals () = Proofview.numgoals

  let dispatch l =
    let l = List.map (fun f -> thaw f) l in
    Proofview.tclDISPATCH l

  let extend lft tac rgt =
    let lft = List.map (fun f -> thaw f) lft in
    let tac = thaw tac in
    let rgt = List.map (fun f -> thaw f) rgt in
    Proofview.tclEXTEND lft tac rgt

  let enter f =
    let f = Proofview.tclIGNORE (thaw f) in
    Proofview.tclINDEPENDENT f

  let focus i j tac =
    Proofview.tclFOCUS i j (thaw tac)

  let cycle = Proofview.cycle

  let shelve () = Proofview.shelve

  let shelve_unifiable () = Proofview.shelve_unifiable

  let new_goal ev =
    Proofview.tclEVARMAP >>= fun sigma ->
    if Evd.mem sigma ev then
      let sigma = Evd.remove_future_goal sigma ev in
      let sigma = Evd.unshelve sigma [ev] in
      Proofview.Unsafe.tclEVARS sigma <*>
        Proofview.Unsafe.tclNEWGOALS [Proofview.with_empty_state ev] <*>
        Proofview.tclUNIT ()
    else throw Tac2ffi.err_notfound

  let is_permutation len l =
    if not (Int.equal len (Array.length l)) then false else
      let items = Array.make len false in
      (* returns true iff [l] (seen as a 1-indexed list) maps ints in [1; len] to [1; len] injectively.
         Thanks to pigeonhole theorem this means [l] is a permutation of [1; len]. *)
      Array.for_all (fun x ->
          if 1 <= x && x <= len && not items.(x-1) then
            let () = items.(x-1) <- true in
            true
          else false)
        l

  let reorder_goals l =
    Proofview.Unsafe.tclGETGOALS >>= fun gls ->
    let len = List.length gls in
    let l = Array.of_list l in
    if not (is_permutation len l) then
      throw (err_invalid_arg (Pp.str "reorder_goals"))
    else
      let gls = Array.of_list gls in
      let gls = List.init len (fun i -> gls.(l.(i) - 1)) in
      Proofview.Unsafe.tclSETGOALS gls

  let unshelve t =
    Proofview.with_shelf (thaw t) >>= fun (gls,v) ->
    let gls = List.map Proofview.with_empty_state gls in
    Proofview.Unsafe.tclGETGOALS >>= fun ogls ->
    Proofview.Unsafe.tclSETGOALS (gls @ ogls) >>= fun () ->
    return v

  let goal () =
    assert_focussed >>= fun () ->
    Proofview.Goal.enter_one @@ fun gl ->
    let sigma = Proofview.Goal.sigma gl in
    let concl = Proofview.Goal.concl gl in
    return (Reductionops.nf_evar sigma concl)

  let hyp id =
    pf_apply @@ fun env _ ->
    let mem = try ignore (Environ.lookup_named id env); true with Not_found -> false in
    if mem then return (EConstr.mkVar id)
    else Tacticals.tclZEROMSG
      (str "Hypothesis " ++ quote (Id.print id) ++ str " not found") (* FIXME: Do something more sensible *)

  let hyp_value id =
    pf_apply @@ fun env _ ->
    match EConstr.lookup_named id env with
    | d -> return (Context.Named.Declaration.get_value d)
    | exception Not_found ->
      Tacticals.tclZEROMSG
      (str "Hypothesis " ++ quote (Id.print id) ++ str " not found") (* FIXME: Do something more sensible *)

  let hyps () =
    pf_apply @@ fun env _ ->
    let open Context in
    let open Named.Declaration in
    let hyps = List.rev (Environ.named_context env) in
    let map = function
    | LocalAssum (id, t) ->
      let t = EConstr.of_constr t in
      Tac2ffi.of_tuple [|
        Tac2ffi.of_ident id.binder_name;
        Tac2ffi.of_option Tac2ffi.of_constr None;
        Tac2ffi.of_constr t;
      |]
    | LocalDef (id, c, t) ->
      let c = EConstr.of_constr c in
      let t = EConstr.of_constr t in
      Tac2ffi.of_tuple [|
        Tac2ffi.of_ident id.binder_name;
        Tac2ffi.of_option Tac2ffi.of_constr (Some c);
        Tac2ffi.of_constr t;
      |]
    in
    return (Tac2ffi.of_list map hyps)

  let refine c =
    let c = thaw c >>= fun c -> Proofview.tclUNIT ((), c, None) in
    Proofview.Goal.enter @@ fun gl ->
    Refine.generic_refine ~typecheck:true c gl

  let solve_constraints () = Refine.solve_constraints

  let with_holes x f = Tacticals.tclRUNWITHHOLES false (thaw x) f

  let progress f = Proofview.tclPROGRESS (thaw f)

  let abstract id f = Abstract.tclABSTRACT id (thaw f)

  let time s f = Proofview.tclTIME s (thaw f)

  let timeout i f = Proofview.tclTIMEOUT i (thaw f)

  let timeoutf f64 f = Proofview.tclTIMEOUTF (Float64.to_float f64) (thaw f)

  let check_interrupt () = Proofview.tclCHECKINTERRUPT

  let clear_err_info (e,_) = (e, Exninfo.null)

  let current_exninfo () =
    return () >>= fun () ->
    set_bt (Exninfo.reify())

  let print_err (e, _) = CErrors.print e

  (* Defined last to avoid shadowing issues in this module *)
  let throw (e, info) = throw ~info e

  let throw_bt (e, _) info =
    Proofview.tclLIFT (Proofview.NonLogical.raise (e, info))
end

(** Fresh *)

module Ltac2Fresh = struct
  module Free = struct
    type t = Nameops.Fresh.t
    let empty = Nameops.Fresh.empty

    let add = Nameops.Fresh.add

    let union = Nameops.Fresh.union

    let of_ids ids = List.fold_right Nameops.Fresh.add ids Nameops.Fresh.empty

    let of_constr c =
      Proofview.tclEVARMAP >>= fun sigma ->
      let rec fold accu c =
        match EConstr.kind sigma c with
        | Constr.Var id -> Nameops.Fresh.add id accu
        | _ -> EConstr.fold sigma fold accu c
      in
      return (fold Nameops.Fresh.empty c)
  end

  (* for backwards compat reasons the ocaml and ltac2 APIs
     exchange the meaning of "fresh" and "next" *)
  let next avoid id =
    let id = Namegen.mangle_id id in
    Nameops.Fresh.fresh id avoid

  let fresh avoid id =
    let id = Namegen.mangle_id id in
    Nameops.Fresh.next id avoid
end

(** Env *)

module Ltac2Env = struct
  let get ids =
    match ids with
    | [] -> None
    | _ :: _ as ids ->
       let (id, path) = List.sep_last ids in
       let path = DirPath.make (List.rev path) in
       let fp = Libnames.make_path path id in
       try Some (Nametab.global_of_path fp) with Not_found -> None

  let expand ids =
    match ids with
    | [] -> []
    | _ :: _ as ids ->
       let (id, path) = List.sep_last ids in
       let path = DirPath.make (List.rev path) in
       let qid = Libnames.make_qualid path id in
       Nametab.locate_all qid

  let path r =
    match Nametab.path_of_global r with
    | fp ->
       let (path, id) = Libnames.repr_path fp in
       let path = DirPath.repr path in
       return (List.rev_append path [id])
    | exception Not_found ->
       throw Tac2ffi.err_notfound

  let instantiate r =
    Proofview.tclENV >>= fun env ->
    Proofview.tclEVARMAP >>= fun sigma ->
    let (sigma, c) = Evd.fresh_global env sigma r in
    Proofview.Unsafe.tclEVARS sigma >>= fun () ->
    return c
end

(** Ind *)

module Ltac2Ind = struct
  type t = Ind.t
  type data = t * Declarations.mutual_inductive_body
  let equal = Ind.UserOrd.equal

  let data ind =
    Proofview.tclENV >>= fun env ->
    if Environ.mem_mind (fst ind) env then
      return (ind, Environ.lookup_mind (fst ind) env)
    else
      throw Tac2ffi.err_notfound

  let repr = fst
  let index = snd

  let nblocks (_, mib) = Array.length mib.Declarations.mind_packets

  let nconstructors ((_, n), mib) =
    Array.length Declarations.(mib.mind_packets.(n).mind_consnames)

  let get_block (ind, mib) n =
    if 0 <= n && n < Array.length mib.Declarations.mind_packets then
      return ((fst ind, n), mib)
    else throw Tac2ffi.err_notfound

  let get_constructor ((mind, n), mib) i =
    let open Declarations in
    let ncons = Array.length mib.mind_packets.(n).mind_consnames in
    if 0 <= i && i < ncons then
      (* WARNING: In the ML API constructors are indexed from 1 for historical
         reasons, but Ltac2 uses 0-indexing instead. *)
      return ((mind, n), i + 1)
    else throw Tac2ffi.err_notfound

  let nparams (_, mib) = mib.Declarations.mind_nparams

  let nparams_uniform (_, mib) = mib.Declarations.mind_nparams_rec

  let get_projections (ind,mib) =
    Declareops.inductive_make_projections ind mib
    |> Option.map (Array.map (fun (p,_) -> Projection.make p false))

  let constructor_nargs ((_,i),mib) =
    let open Declarations in
    mib.mind_packets.(i).mind_consnrealargs

  let constructor_ndecls ((_,i),mib) =
    let open Declarations in
    mib.mind_packets.(i).mind_consnrealdecls

  let print ind = Nametab.pr_global_env Id.Set.empty (IndRef ind)
end

(** Constructor *)
module Ltac2Constructor = struct
  type t = Construct.t

  let equal = Construct.UserOrd.equal

  let inductive (ind, _) = ind

  let index (_, i) =
    (* WARNING: ML constructors are 1-indexed but Ltac2 constructors are 0-indexed *)
    i-1

  let print ctor =
    Nametab.pr_global_env Id.Set.empty (ConstructRef ctor)
end

(** Schemes *)

module Ltac2Scheme = struct
  type kind = string

  let lookup = DeclareScheme.lookup_scheme_opt

  let rect_dep = "rect_dep"
  let rec_dep = "rec_dep"
  let ind_dep = "ind_dep"
  let sind_dep = "sind_dep"
  let ind_nodep = "ind_nodep"
  let rec_nodep = "rec_nodep"
  let rect_nodep = "rect_nodep"
  let sind_nodep = "sind_nodep"
  let eq_dec = "eq_dec"
  let dec_lb = "dec_lb"
  let dec_bl = "dec_bl"
  let beq = "beq"
  let congr = "congr"
  let rew_fwd_r_dep = "rew_fwd_r_dep"
  let rew_r_dep = "rew_r_dep"
  let rew_r = "rew_r"
  let rew_fwd_dep = "rew_fwd_dep"
  let rew_dep = "rew_dep"
  let rew = "rew"
  let sym_involutive = "sym_involutive"
  let sym = "sym"
  let scase_nodep = "scase_nodep"
  let scase_dep = "scase_dep"
  let casep_nodep = "casep_nodep"
  let casep_dep = "casep_dep"
  let case_nodep = "case_nodep"
  let case_dep = "case_dep"
end

(** Proj *)

module Ltac2Proj = struct
  type t = Projection.t
  let equal = Projection.UserOrd.equal
  let ind = Projection.inductive

  let index = Projection.arg

  let unfolded = Projection.unfolded

  let set_unfolded p b = Projection.make (Projection.repr p) b

  let of_constant c =
    Structures.PrimitiveProjections.find_opt c |> Option.map (fun p -> Projection.make p false)

  let to_constant p = Some (Projection.constant p)

  let print p =
    Nametab.pr_global_env Id.Set.empty (ConstRef (Projection.constant p))
end

(** Module *)

module Ltac2Module = struct
  type t = ModPath.t
  let equal = ModPath.equal

  let to_message m =
  (* XXX use ModPath.print instead? (nametab is ambiguous since there's no single nametab)
     or expose ModPath.print as a separate external? *)
  try Nametab.Modules.pr m
  with Not_found ->
  try Nametab.ModTypes.pr m
  with Not_found ->
  try Nametab.OpenMods.pr (DirOpenModule m)
  with Not_found ->
  try Nametab.OpenMods.pr (DirOpenModtype m)
  with Not_found ->
    CErrors.anomaly Pp.(str "Unknown module or modtype " ++ ModPath.print m)

  let is_openmod m =
    ModPath.subpath m (Global.current_modpath())

  (* Find info about open module [m] in [senv_l] describing the open
     modules of some safe env with current module [senv_m].
     Returns [None] if [m] is the library, [Some v] if [m] is some inner open module. *)
  let rec find_openmod m senv_m senv_l =
    let open ModPath in
    match senv_m, senv_l with
    | MPbound _, _ -> assert false
    | MPfile _, [] -> assert (ModPath.equal m senv_m); None
    | MPfile _, _ :: _ -> assert false
    | MPdot (m0, _), is_modtype :: rest ->
       if ModPath.equal m senv_m then Some is_modtype
       else find_openmod m m0 rest
    | MPdot _, [] -> assert false

  (* Assuming [m] is currently open, tell whether it is modtype. *)
  let open_module_is_modtype m =
    let senv = Global.safe_env() in
    match find_openmod m (Safe_typing.current_modpath senv) (Safe_typing.module_is_modtype senv) with
    | None -> false
    | Some b -> b

  let open_module_is_functor m =
    let senv = Global.safe_env() in
    match find_openmod m (Safe_typing.current_modpath senv) (Safe_typing.module_num_parameters senv) with
    | None -> false
    | Some nparams -> not (Int.equal nparams 0)

  let is_modtype m env _ =
    if is_openmod m then open_module_is_modtype m
    else
      try ignore (Environ.lookup_modtype m env); true
      with Not_found -> false

  let is_functor m env _ =
    if is_openmod m then open_module_is_functor m
    else
      let modbody_is_functor m = match Mod_declarations.mod_type m with
        | NoFunctor _ -> false
        | MoreFunctor _ -> true
      in
      match Environ.lookup_module m env with
      | m -> modbody_is_functor m
      | exception Not_found -> match Environ.lookup_modtype m env with
                               | m -> modbody_is_functor m
                               | exception Not_found -> assert false

  let is_bound_module = function
  | MPbound _ -> true
  | MPfile _ | MPdot _ -> false

  let is_library = function
  | MPfile _ -> true
  | MPbound _ | MPdot _ -> false

  let is_open = is_openmod

  let parent_module = function
  | MPdot (m, _) -> Some m
  | MPbound _ | MPfile _ -> None

  open GlobRef
  let module_of_reference = function
  | VarRef _ -> throw (Invalid_argument "module_of_reference")
  | ConstRef c -> return (Constant.modpath c)
  | IndRef (mind,_) | ConstructRef ((mind,_),_) -> return (MutInd.modpath mind)

  let current_module () = Global.current_modpath ()

  let loaded_libraries () =
    List.map (fun dp -> MPfile dp) (Library.loaded_libraries())

  module Field = struct
    open ModField
    type t = ModField.t

    let handle f handler =
      let (handle_submodule, handle_reference, handle_rewrule) = handler in
      match f with
      | Ref x -> handle_reference x
      | Submodule x -> handle_submodule x
      | Rewrule -> handle_rewrule ()
  end

  let openmod_revstruct m senv =
    let rec close senv modtype =
      let curm = Safe_typing.current_modpath senv in
      if ModPath.equal m curm then senv
      else
        let l = match curm with
          | MPdot (_, l) -> l
          | _ -> assert false
        in
        match modtype with
        | [] -> assert false
        | false :: modtype ->
           (* None: type constraint of submodule doesn't matter since we
              will anyway only return "Submodule M" and not look at its
              contents *)
           close (snd @@ Safe_typing.end_module l None senv) modtype
        | true :: modtype -> close (snd @@ Safe_typing.end_modtype l senv) modtype
    in
    let modtype = Safe_typing.module_is_modtype senv in
    let senv = close senv modtype in
    Safe_typing.structure_body_of_safe_env senv

  let contents m =
    let body =
      if is_open m then
        (* XXX not sure what this does with side effects *)
        Some (List.rev (openmod_revstruct m (Global.safe_env())))
      else
        match Environ.lookup_module m (Global.env()) with
        | exception Not_found -> (* modtype *) None
        | body -> match Mod_declarations.mod_type body with
                  | MoreFunctor _ -> (* functor *) None
                  | NoFunctor body -> Some body
    in
    let to_field (lab, f) : ModField.t = match (f:_ Declarations.structure_field_body) with
      | SFBconst _ ->
         let kn = KerName.make m lab in
         Ref (ConstRef (Global.constant_of_delta_kn kn))
      | SFBmind _ ->
         let kn = KerName.make m lab in
         Ref (IndRef ((Global.mind_of_delta_kn kn, 0)))
      | SFBrules _ -> Rewrule
      | SFBmodule _ -> Submodule (MPdot (m, lab))
      | SFBmodtype _ -> Submodule (MPdot (m, lab))
    in
    Option.map (List.map to_field) body
end

(** Rewrite *)

module Ltac2Rewrite = struct
  module Strategy = struct
    type t = Rewrite.strategy

    let id           = Rewrite.Strategies.id
    let fail         = Rewrite.Strategies.fail
    let refl         = Rewrite.Strategies.refl
    let progress     = Rewrite.Strategies.progress
    let seq          = Rewrite.Strategies.seq
    let seqs         = Rewrite.Strategies.seqs
    let choice       = Rewrite.Strategies.choice
    let choices      = Rewrite.Strategies.choices
    let try_         = Rewrite.Strategies.try_
    let fix_         = Tac2tactics.RewriteStrats.fix
    let any          = Rewrite.Strategies.any
    let repeat       = Rewrite.Strategies.repeat
    let one_subterm  = Rewrite.Strategies.one_subterm
    let all_subterms = Rewrite.Strategies.all_subterms
    let bottomup     = Rewrite.Strategies.bottomup
    let topdown      = Rewrite.Strategies.topdown
    let innermost    = Rewrite.Strategies.innermost
    let outermost    = Rewrite.Strategies.outermost
    let hints        = Tac2tactics.RewriteStrats.hints
    let old_hints    = Tac2tactics.RewriteStrats.old_hints
    let one_lemma    = Tac2tactics.RewriteStrats.one_lemma
    let lemmas       = Tac2tactics.RewriteStrats.lemmas
    let fold         = Rewrite.Strategies.fold
    let eval         = Rewrite.Strategies.reduce
    let matches      = Rewrite.Strategies.matches

    let tactic = Tac2tactics.wrap_tactic_call
  end

  let rewrite_strat = Tac2tactics.rewrite_strat
end

let () = define "tac_rewrite_strat" (rewstrategy @-> option ident @-> tac unit) Ltac2Rewrite.rewrite_strat

let () = define "rewstrat_id" (ret rewstrategy) Ltac2Rewrite.Strategy.id
let () = define "rewstrat_fail" (ret rewstrategy) Ltac2Rewrite.Strategy.fail
let () = define "rewstrat_refl" (ret rewstrategy) Ltac2Rewrite.Strategy.refl
let () = define "rewstrat_progress" (rewstrategy @-> ret rewstrategy) Ltac2Rewrite.Strategy.progress
let () = define "rewstrat_seq" (rewstrategy @-> rewstrategy @-> ret rewstrategy) Ltac2Rewrite.Strategy.seq
let () = define "rewstrat_seqs" (list rewstrategy @-> ret rewstrategy) Ltac2Rewrite.Strategy.seqs
let () = define "rewstrat_choice" (rewstrategy @-> rewstrategy @-> ret rewstrategy) Ltac2Rewrite.Strategy.choice
let () = define "rewstrat_choices" (list rewstrategy @-> ret rewstrategy) Ltac2Rewrite.Strategy.choices
let () = define "rewstrat_try" (rewstrategy @-> ret rewstrategy) Ltac2Rewrite.Strategy.try_
let () = define "rewstrat_fix" (closure @-> tac rewstrategy) Ltac2Rewrite.Strategy.fix_
let () = define "rewstrat_any" (rewstrategy @-> ret rewstrategy) Ltac2Rewrite.Strategy.any
let () = define "rewstrat_repeat" (rewstrategy @-> ret rewstrategy) Ltac2Rewrite.Strategy.repeat
let () = define "rewstrat_one_subterm" (rewstrategy @-> ret rewstrategy) Ltac2Rewrite.Strategy.one_subterm
let () = define "rewstrat_all_subterms" (rewstrategy @-> ret rewstrategy) Ltac2Rewrite.Strategy.all_subterms
let () = define "rewstrat_bottomup" (rewstrategy @-> ret rewstrategy) Ltac2Rewrite.Strategy.bottomup
let () = define "rewstrat_topdown" (rewstrategy @-> ret rewstrategy) Ltac2Rewrite.Strategy.topdown
let () = define "rewstrat_innermost" (rewstrategy @-> ret rewstrategy) Ltac2Rewrite.Strategy.innermost
let () = define "rewstrat_outermost" (rewstrategy @-> ret rewstrategy) Ltac2Rewrite.Strategy.outermost
let () = define "rewstrat_hints" (ident @-> ret rewstrategy) Ltac2Rewrite.Strategy.hints
let () = define "rewstrat_old_hints" (ident @-> ret rewstrategy) Ltac2Rewrite.Strategy.old_hints
let () = define "rewstrat_one_lemma" (preterm @-> bool @-> ret rewstrategy) Ltac2Rewrite.Strategy.one_lemma
let () = define "rewstrat_lemmas" (list preterm @-> ret rewstrategy) Ltac2Rewrite.Strategy.lemmas
let () = define "rewstrat_fold" (constr @-> ret rewstrategy) Ltac2Rewrite.Strategy.fold
let () = define "rewstrat_eval" (reduction @-> ret rewstrategy) Ltac2Rewrite.Strategy.eval
let () = define "rewstrat_matches" (pattern @-> ret rewstrategy) Ltac2Rewrite.Strategy.matches

let () = define "rewstrat_tactic" (fun3 constr constr (option constr) rewrite_result @-> ret rewstrategy) Ltac2Rewrite.Strategy.tactic

(** TransparentState *)

module Ltac2TransparentState = struct
  type t = TransparentState.t
  type strategy_level = Conv_oracle.level

  open TransparentState

  let empty = TransparentState.empty
  let full = TransparentState.full
  let current = Tac2tactics.current_transparent_state

  let union ts1 ts2 =
    { tr_var = Id.Pred.union ts1.tr_var ts2.tr_var ;
      tr_cst = Cpred.union ts1.tr_cst ts2.tr_cst ;
      tr_prj = PRpred.union ts1.tr_prj ts2.tr_prj }

  let inter ts1 ts2 =
    { tr_var = Id.Pred.inter ts1.tr_var ts2.tr_var ;
      tr_cst = Cpred.inter ts1.tr_cst ts2.tr_cst ;
      tr_prj = PRpred.inter ts1.tr_prj ts2.tr_prj }

  let diff ts1 ts2 =
    { tr_var = Id.Pred.diff ts1.tr_var ts2.tr_var ;
      tr_cst = Cpred.diff ts1.tr_cst ts2.tr_cst ;
      tr_prj = PRpred.diff ts1.tr_prj ts2.tr_prj }

  let add_constant c ts =
    { tr_var = ts.tr_var ;
      tr_cst = Cpred.add c ts.tr_cst ;
      tr_prj = ts.tr_prj }

  let add_proj p ts =
    { tr_var = ts.tr_var ;
      tr_cst = ts.tr_cst ;
      tr_prj = PRpred.add (Projection.repr p) ts.tr_prj }

  let add_var v ts =
    { tr_var = Id.Pred.add v ts.tr_var ;
      tr_cst = ts.tr_cst ;
      tr_prj = ts.tr_prj }

  let remove_constant c ts =
    { tr_var = ts.tr_var ;
      tr_cst = Cpred.remove c ts.tr_cst ;
      tr_prj = ts.tr_prj }

  let remove_proj p ts =
    { tr_var = ts.tr_var ;
      tr_cst = ts.tr_cst ;
      tr_prj = PRpred.remove (Projection.repr p) ts.tr_prj }

  let remove_var v ts =
    { tr_var = Id.Pred.remove v ts.tr_var ;
      tr_cst = ts.tr_cst ;
      tr_prj = ts.tr_prj }

  let mem_constant c ts = Cpred.mem c ts.tr_cst
  let mem_proj p ts = PRpred.mem (Projection.repr p) ts.tr_prj
  let mem_var v ts = Id.Pred.mem v ts.tr_var

  let with_strategy = Tac2tactics.with_strategy
end

let () = define "empty_transparent_state" (ret transparent_state) Ltac2TransparentState.empty
let () = define "full_transparent_state" (ret transparent_state) Ltac2TransparentState.full
let () = define "current_transparent_state" (unit @-> tac transparent_state) Ltac2TransparentState.current

let () = define "union_transparent_state"
           (transparent_state @-> transparent_state @-> ret transparent_state)
           Ltac2TransparentState.union
let () = define "inter_transparent_state"
           (transparent_state @-> transparent_state @-> ret transparent_state)
           Ltac2TransparentState.inter
let () = define "diff_transparent_state"
           (transparent_state @-> transparent_state @-> ret transparent_state)
           Ltac2TransparentState.diff

let () = define "add_constant_transparent_state"
           (constant @-> transparent_state @-> ret transparent_state)
           Ltac2TransparentState.add_constant
let () = define "add_proj_transparent_state"
           (projection @-> transparent_state @-> ret transparent_state)
           Ltac2TransparentState.add_proj
let () = define "add_var_transparent_state"
           (ident @-> transparent_state @-> ret transparent_state)
           Ltac2TransparentState.add_var

let () = define "remove_constant_transparent_state"
           (constant @-> transparent_state @-> ret transparent_state)
           Ltac2TransparentState.remove_constant
let () = define "remove_proj_transparent_state"
           (projection @-> transparent_state @-> ret transparent_state)
           Ltac2TransparentState.remove_proj
let () = define "remove_var_transparent_state"
           (ident @-> transparent_state @-> ret transparent_state)
           Ltac2TransparentState.remove_var

let () = define "mem_constant_transparent_state"
           (constant @-> transparent_state @-> ret bool)
           Ltac2TransparentState.mem_constant
let () = define "mem_proj_transparent_state"
           (projection @-> transparent_state @-> ret bool)
           Ltac2TransparentState.mem_proj
let () = define "mem_var_transparent_state"
           (ident @-> transparent_state @-> ret bool)
           Ltac2TransparentState.mem_var

let () = define "with_strategy"
           (strategy_level @-> list reference @-> thunk valexpr @-> tac valexpr)
           Ltac2TransparentState.with_strategy

(** Unification *)

let to_conv_pb v = match Tac2ffi.to_int v with
  | 0 -> Conversion.CONV
  | 1 -> Conversion.CUMUL
  | _ -> assert false

module Ltac2Unification = struct
  type conv_flag = Evd.conv_pb

  let conv pb ts c1 c2 =
    pf_apply @@ fun env sigma ->
                match Reductionops.infer_conv ~pb ~ts env sigma c1 c2 with
                | Some sigma -> Proofview.Unsafe.tclEVARS sigma <*> return true
                | None -> return false

  let unify = Tac2tactics.evarconv_unify
end

let () = define "infer_conv" (to_conv_pb @--> transparent_state @-> constr @-> constr @-> tac bool) Ltac2Unification.conv
let () = define "evarconv_unify" (transparent_state @-> constr @-> constr @-> tac unit) Ltac2Unification.unify

(** FSet/FMap *)
module MapTagDyn = Dyn.Make()

type ('a,'set,'map) map_tag = ('a * 'set * 'map) MapTagDyn.tag

type any_map_tag = Any : _ map_tag -> any_map_tag
type tagged_set = TaggedSet : (_,'set,_) map_tag * 'set -> tagged_set
type tagged_map = TaggedMap : (_,_,'map) map_tag * 'map -> tagged_map

let map_tag_ext : any_map_tag Tac2dyn.Val.tag = Tac2dyn.Val.create "fmap_tag_"
let map_tag_repr = Tac2ffi.repr_ext map_tag_ext

let set_ext : tagged_set Tac2dyn.Val.tag = Tac2dyn.Val.create "fset_"
let set_repr = Tac2ffi.repr_ext set_ext
let tag_set tag s = Tac2ffi.repr_of set_repr (TaggedSet (tag,s))

let map_ext : tagged_map Tac2dyn.Val.tag = Tac2dyn.Val.create "fmap_"
let map_repr = Tac2ffi.repr_ext map_ext
let tag_map tag m = Tac2ffi.repr_of map_repr (TaggedMap (tag,m))

module type MapType = sig
  (* to have less boilerplate we use S.elt rather than declaring a toplevel type t *)
  module S : CSig.USetS
  module M : CMap.UExtS with type key = S.elt and module Set := S
  type valmap
  val valmap_eq : (valmap, valexpr M.t) Util.eq
  val repr : S.elt Tac2ffi.repr
end

module MapTypeV = struct
  type _ t = Map : (module MapType with type S.elt = 't and type S.t = 'set and type valmap = 'map)
    -> ('t * 'set * 'map) t
end

module MapMap = MapTagDyn.Map(MapTypeV)

let maps = ref MapMap.empty

let register_map ?(plugin=ltac2_plugin) ~tag_name x =
  let tag = MapTagDyn.create (plugin^":"^tag_name) in
  let () = maps := MapMap.add tag (Map x) !maps in
  let () = define ~plugin tag_name (ret map_tag_repr) (Any tag) in
  tag

let get_map (type t s m) (tag:(t,s,m) map_tag)
  : (module MapType with type S.elt = t and type S.t = s and type valmap = m) =
  let Map v = MapMap.find tag !maps in
  v

let map_tag_eq (type a b c a' b' c') (t1:(a,b,c) map_tag) (t2:(a',b',c') map_tag)
  : (a*b*c,a'*b'*c') Util.eq option
  = MapTagDyn.eq t1 t2

let assert_map_tag_eq t1 t2 = match map_tag_eq t1 t2 with
  | Some v -> v
  | None -> assert false

let ident_map_tag : _ map_tag = register_map ~tag_name:"fmap_ident_tag" (module struct
    module S = Id.Set
    module M = Id.Map
    let repr = Tac2ffi.ident
    type valmap = valexpr M.t
    let valmap_eq = Refl
  end)

let int_map_tag : _ map_tag = register_map ~tag_name:"fmap_int_tag" (module struct
    module S = Int.Set
    module M = Int.Map
    let repr = Tac2ffi.int
    type valmap = valexpr M.t
    let valmap_eq = Refl
  end)

let string_map_tag : _ map_tag = register_map ~tag_name:"fmap_string_tag" (module struct
    module S = String.Set
    module M = String.Map
    let repr = Tac2ffi.string
    type valmap = valexpr M.t
    let valmap_eq = Refl
  end)

let inductive_map_tag : _ map_tag = register_map ~tag_name:"fmap_inductive_tag" (module struct
    module S = Indset_env
    module M = Indmap_env
    let repr = inductive
    type valmap = valexpr M.t
    let valmap_eq = Refl
  end)

let constructor_map_tag : _ map_tag = register_map ~tag_name:"fmap_constructor_tag" (module struct
    module S = Constrset_env
    module M = Constrmap_env
    let repr = Tac2ffi.constructor
    type valmap = valexpr M.t
    let valmap_eq = Refl
  end)

let constant_map_tag : _ map_tag = register_map ~tag_name:"fmap_constant_tag" (module struct
    module S = Cset_env
    module M = Cmap_env
    let repr = Tac2ffi.constant
    type valmap = valexpr M.t
    let valmap_eq = Refl
  end)


module Ltac2FSet = struct
  module Tags = struct
    let ident_tag = ident_map_tag
    let int_tag = int_map_tag
    let inductive_tag = inductive_map_tag
    let constructor_tag = constructor_map_tag
    let constant_tag = constant_map_tag
    let string_tag = string_map_tag
  end
  let empty (Any tag) =
    let (module V) = get_map tag in
    tag_set tag V.S.empty
  let is_empty (TaggedSet (tag,s)) =
    let (module V) = get_map tag in
    V.S.is_empty s

  let mem x (TaggedSet (tag,s)) =
    let (module V) = get_map tag in
    V.S.mem (repr_to V.repr x) s

  let add x (TaggedSet (tag,s)) =
    let (module V) = get_map tag in
    tag_set tag (V.S.add (repr_to V.repr x) s)

  let remove x (TaggedSet (tag, s)) =
    let (module V) = get_map tag in
    tag_set tag (V.S.remove (repr_to V.repr x) s)

  let union (TaggedSet (tag,s1)) (TaggedSet (tag',s2)) =
    let Refl = assert_map_tag_eq tag tag' in
    let (module V) = get_map tag in
    tag_set tag (V.S.union s1 s2)

  let inter (TaggedSet (tag,s1)) (TaggedSet (tag',s2)) =
    let Refl = assert_map_tag_eq tag tag' in
    let (module V) = get_map tag in
    tag_set tag (V.S.inter s1 s2)

  let diff (TaggedSet (tag,s1)) (TaggedSet (tag',s2)) =
    let Refl = assert_map_tag_eq tag tag' in
    let (module V) = get_map tag in
    tag_set tag (V.S.diff s1 s2)

  let equal (TaggedSet (tag,s1)) (TaggedSet (tag',s2)) =
    let Refl = assert_map_tag_eq tag tag' in
    let (module V) = get_map tag in
    V.S.equal s1 s2

  let subset (TaggedSet (tag,s1)) (TaggedSet (tag',s2)) =
    let Refl = assert_map_tag_eq tag tag' in
    let (module V) = get_map tag in
    V.S.subset s1 s2

  let cardinal (TaggedSet (tag,s)) =
    let (module V) = get_map tag in
    V.S.cardinal s

  let elements (TaggedSet (tag,s)) =
    let (module V) = get_map tag in
    Tac2ffi.of_list (repr_of V.repr) (V.S.elements s)
end

module Ltac2FMap = struct
  let empty (Any (tag)) =
    let (module V) = get_map tag in
    let Refl = V.valmap_eq in
    tag_map tag V.M.empty

  let is_empty (TaggedMap (tag,m)) =
    let (module V) = get_map tag in
    let Refl = V.valmap_eq in
    V.M.is_empty m

  let mem x (TaggedMap (tag,m)) =
    let (module V) = get_map tag in
    let Refl = V.valmap_eq in
    V.M.mem (repr_to V.repr x) m

  let add x v (TaggedMap (tag,m)) =
    let (module V) = get_map tag in
    let Refl = V.valmap_eq in
    tag_map tag (V.M.add (repr_to V.repr x) v m)

  let remove x (TaggedMap (tag,m)) =
    let (module V) = get_map tag in
    let Refl = V.valmap_eq in
    tag_map tag (V.M.remove (repr_to V.repr x) m)

  let find_opt x (TaggedMap (tag,m)) =
    let (module V) = get_map tag in
    let Refl = V.valmap_eq in
    V.M.find_opt (repr_to V.repr x) m

  let mapi f (TaggedMap (tag,m)) =
    let (module V) = get_map tag in
    let Refl = V.valmap_eq in
    let module Monadic = V.M.Monad(Proofview.Monad) in
    Monadic.mapi (fun k v -> apply f [repr_of V.repr k;v]) m >>= fun m ->
    return (tag_map tag m)

  let fold f (TaggedMap (tag,m)) acc =
    let (module V) = get_map tag in
    let Refl = V.valmap_eq in
    let module Monadic = V.M.Monad(Proofview.Monad) in
    Monadic.fold (fun k v acc -> apply f [repr_of V.repr k;v;acc]) m acc

  let cardinal (TaggedMap (tag,m)) =
    let (module V) = get_map tag in
    let Refl = V.valmap_eq in
    V.M.cardinal m

  let bindings (TaggedMap (tag,m)) =
    let (module V) = get_map tag in
    let Refl = V.valmap_eq in
    Tac2ffi.(of_list (of_pair (repr_of V.repr) identity) (V.M.bindings m))

  let domain (TaggedMap (tag,m)) =
    let (module V) = get_map tag in
    let Refl = V.valmap_eq in
    tag_set tag (V.M.domain m)
end

(** Ltac2 API *)

module Ltac2 = struct
  (** Built-in types *)
  type int = Int.t
  type string = String.t
  type char = Char.t
  type ident = Id.t
  type uint63 = Uint63.t
  type float = Float64.t
  type pstring = Pstring.t
  type meta = Constr.metavariable
  type evar = Evar.t
  type sort = Sorts.t
  type cast = Constr.cast_kind
  type instance = EConstr.EInstance.t
  type constant = Constant.t
  type inductive = Ind.t
  type constructor = Construct.t
  type projection = Projection.t
  type pattern = Pattern.constr_pattern
  type constr = EConstr.t
  type preterm = Ltac_pretype.closed_glob_constr
  type binder = Name.t EConstr.binder_annot * EConstr.types
  type message = Pp.t
  type ('a, 'b, 'c, 'd) format = Tac2types.format list
  type nonrec 'a array = 'a array
  type err = Exninfo.iexn
  type exn = Exninfo.iexn
  type exninfo = Exninfo.info

  module Array            = Ltac2Array
  module Char             = Ltac2Char
  module Constant         = Ltac2Constant
  module Constr           = Ltac2Constr
  module Constructor      = Ltac2Constructor
  module Control          = Ltac2Control
  module Env              = Ltac2Env
  module Evar             = Ltac2Evar
  module Float            = Ltac2Float
  module Fresh            = Ltac2Fresh
  module Ident            = Ltac2Ident
  module Ind              = Ltac2Ind
  module Int              = Ltac2Int
  module Message          = Ltac2Message
  module Meta             = Ltac2Meta
  module Module           = Ltac2Module
  module Pattern          = Ltac2Pattern
  module Proj             = Ltac2Proj
  module Pstring          = Ltac2Pstring
  module Rewrite          = Ltac2Rewrite
  module Scheme           = Ltac2Scheme
  module Std              = Tac2stdlib.Ltac2Std
  module String           = Ltac2String
  module Uint63           = Ltac2Uint63
  module FSet             = Ltac2FSet
  module FMap             = Ltac2FMap
  module TransparentState = Ltac2TransparentState
  module Unification      = Ltac2Unification
end
