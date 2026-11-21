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
open Names
open Constr
open Declarations
open Environ
open CClosure

module RelDecl = Context.Rel.Declaration
module NamedDecl = Context.Named.Declaration

type fhandle

external setup : unit -> unit = "rconv_setup"
external constr_tag : Constr.t -> int = "rconv_constr_tag"
external conv_raw : Obj.t -> Obj.t = "rconv_conv"

external fc_get_atom : fhandle -> Obj.t = "rconv_fc_get_atom"
external fc_array_lift : fhandle -> int = "rconv_fc_array_lift"
external fc_array_parray : fhandle -> fhandle Parray.t = "rconv_fc_array_parray"
external fc_lift : int -> fhandle -> fhandle = "rconv_fc_lift"
external fc_mk_prim : int -> Obj.t -> fhandle = "rconv_fc_mk_prim"
external fc_mk_construct : constructor -> UVars.Instance.t -> fhandle = "rconv_fc_mk_construct"
external fc_mk_const : Constant.t -> UVars.Instance.t -> fhandle = "rconv_fc_mk_const"
external fc_mkfapp : fhandle -> fhandle array -> fhandle = "rconv_fc_mkfapp"
external fc_mk_array : UVars.Instance.t -> fhandle Parray.t -> fhandle -> fhandle = "rconv_fc_mk_array"

let enabled = ref (match Sys.getenv_opt "ROCQ_RUST_CONV" with
  | None | Some ("" | "0") -> false
  | Some _ -> true)

(** Primitive operations, over handles to Rust closures *)

module RNativeEntries =
  struct
    type elem = fhandle
    type args = fhandle array
    type evd = unit
    type uinstance = UVars.Instance.t
    type lft = int

    let mk_construct c = fc_mk_construct c UVars.Instance.empty

    let get = Array.get

    let get_int () e : Uint63.t = Obj.obj (fc_get_atom e)

    let get_float () e : Float64.t = Obj.obj (fc_get_atom e)

    let get_string () e : Pstring.t = Obj.obj (fc_get_atom e)

    let get_parray () e = fc_array_lift e, fc_array_parray e

    let trivial_lift n = Int.equal n 0

    let lift n e = fc_lift n e

    let dummy = lazy (fc_mk_prim 0 (Obj.repr Uint63.zero))

    let current_retro = ref Retroknowledge.empty
    let defined_int = ref false
    let fint = ref dummy

    let init_int retro =
      match retro.Retroknowledge.retro_int63 with
      | Some c ->
        defined_int := true;
        fint := Lazy.from_val (fc_mk_const c UVars.Instance.empty)
      | None -> defined_int := false

    let defined_float = ref false
    let ffloat = ref dummy

    let init_float retro =
      match retro.Retroknowledge.retro_float64 with
      | Some c ->
        defined_float := true;
        ffloat := Lazy.from_val (fc_mk_const c UVars.Instance.empty)
      | None -> defined_float := false

    let defined_string = ref false

    let init_string retro =
      match retro.Retroknowledge.retro_string with
      | Some _ -> defined_string := true
      | None -> defined_string := false

    let defined_bool = ref false
    let ftrue = ref dummy
    let ffalse = ref dummy

    let init_bool retro =
      match retro.Retroknowledge.retro_bool with
      | Some (ct,cf) ->
        defined_bool := true;
        ftrue := Lazy.from_val (mk_construct ct);
        ffalse := Lazy.from_val (mk_construct cf);
      | None -> defined_bool :=false

    let defined_carry = ref false
    let fC0 = ref dummy
    let fC1 = ref dummy

    let init_carry retro =
      match retro.Retroknowledge.retro_carry with
      | Some(c0,c1) ->
        defined_carry := true;
        fC0 := Lazy.from_val (mk_construct c0);
        fC1 := Lazy.from_val (mk_construct c1);
      | None -> defined_carry := false

    let defined_pair = ref false
    let fPair = ref dummy

    let init_pair retro =
      match retro.Retroknowledge.retro_pair with
      | Some c ->
        defined_pair := true;
        fPair := Lazy.from_val (mk_construct c);
      | None -> defined_pair := false

    let defined_cmp = ref false
    let fEq = ref dummy
    let fLt = ref dummy
    let fGt = ref dummy

    let init_cmp retro =
      match retro.Retroknowledge.retro_cmp with
      | Some (cEq, cLt, cGt) ->
        defined_cmp := true;
        fEq := Lazy.from_val (mk_construct cEq);
        fLt := Lazy.from_val (mk_construct cLt);
        fGt := Lazy.from_val (mk_construct cGt);
      | None -> defined_cmp := false

    let defined_f_cmp = ref false
    let fFEq = ref dummy
    let fFLt = ref dummy
    let fFGt = ref dummy
    let fFNotComparable = ref dummy

    let init_f_cmp retro =
      match retro.Retroknowledge.retro_f_cmp with
      | Some (cFEq, cFLt, cFGt, cFNotComparable) ->
        defined_f_cmp := true;
        fFEq := Lazy.from_val (mk_construct cFEq);
        fFLt := Lazy.from_val (mk_construct cFLt);
        fFGt := Lazy.from_val (mk_construct cFGt);
        fFNotComparable := Lazy.from_val (mk_construct cFNotComparable);
      | None -> defined_f_cmp := false

    let defined_f_class = ref false
    let fPNormal = ref dummy
    let fNNormal = ref dummy
    let fPSubn = ref dummy
    let fNSubn = ref dummy
    let fPZero = ref dummy
    let fNZero = ref dummy
    let fPInf = ref dummy
    let fNInf = ref dummy
    let fNaN = ref dummy

    let init_f_class retro =
      match retro.Retroknowledge.retro_f_class with
      | Some (cPNormal, cNNormal, cPSubn, cNSubn, cPZero, cNZero,
              cPInf, cNInf, cNaN) ->
        defined_f_class := true;
        fPNormal := Lazy.from_val (mk_construct cPNormal);
        fNNormal := Lazy.from_val (mk_construct cNNormal);
        fPSubn := Lazy.from_val (mk_construct cPSubn);
        fNSubn := Lazy.from_val (mk_construct cNSubn);
        fPZero := Lazy.from_val (mk_construct cPZero);
        fNZero := Lazy.from_val (mk_construct cNZero);
        fPInf := Lazy.from_val (mk_construct cPInf);
        fNInf := Lazy.from_val (mk_construct cNInf);
        fNaN := Lazy.from_val (mk_construct cNaN);
      | None -> defined_f_class := false

    let defined_array = ref false

    let init_array retro =
      defined_array := Option.has_some retro.Retroknowledge.retro_array

    let init env =
      current_retro := Environ.retroknowledge env;
      init_int !current_retro;
      init_float !current_retro;
      init_string !current_retro;
      init_bool !current_retro;
      init_carry !current_retro;
      init_pair !current_retro;
      init_cmp !current_retro;
      init_f_cmp !current_retro;
      init_f_class !current_retro;
      init_array !current_retro

    let check_env env =
      if not (!current_retro == Environ.retroknowledge env) then init env

    let check_int env =
      check_env env;
      assert (!defined_int)

    let check_float env =
      check_env env;
      assert (!defined_float)

    let check_string env =
      check_env env;
      assert (!defined_string)

    let check_bool env =
      check_env env;
      assert (!defined_bool)

    let check_carry env =
      check_env env;
      assert (!defined_carry && !defined_int)

    let check_pair env =
      check_env env;
      assert (!defined_pair && !defined_int)

    let check_cmp env =
      check_env env;
      assert (!defined_cmp)

    let check_f_cmp env =
      check_env env;
      assert (!defined_f_cmp)

    let check_f_class env =
      check_env env;
      assert (!defined_f_class)

    let check_array env =
      check_env env;
      assert (!defined_array)

    let mkInt env i =
      check_int env;
      fc_mk_prim 0 (Obj.repr i)

    let mkFloat env f =
      check_float env;
      fc_mk_prim 1 (Obj.repr f)

    let mkString env s =
      check_string env;
      fc_mk_prim 2 (Obj.repr s)

    let mkBool env b =
      check_bool env;
      if b then Lazy.force !ftrue else Lazy.force !ffalse

    let mkCarry env b e =
      check_carry env;
      fc_mkfapp (Lazy.force (if b then !fC1 else !fC0)) [|Lazy.force !fint;e|]

    let mkIntPair env e1 e2 =
      check_pair env;
      fc_mkfapp (Lazy.force !fPair) [|Lazy.force !fint;Lazy.force !fint;e1;e2|]

    let mkFloatIntPair env f i =
      check_pair env;
      check_float env;
      fc_mkfapp (Lazy.force !fPair) [|Lazy.force !ffloat;Lazy.force !fint;f;i|]

    let mkLt env =
      check_cmp env;
      Lazy.force !fLt

    let mkEq env =
      check_cmp env;
      Lazy.force !fEq

    let mkGt env =
      check_cmp env;
      Lazy.force !fGt

    let mkFLt env =
      check_f_cmp env;
      Lazy.force !fFLt

    let mkFEq env =
      check_f_cmp env;
      Lazy.force !fFEq

    let mkFGt env =
      check_f_cmp env;
      Lazy.force !fFGt

    let mkFNotComparable env =
      check_f_cmp env;
      Lazy.force !fFNotComparable

    let mkPNormal env =
      check_f_class env;
      Lazy.force !fPNormal

    let mkNNormal env =
      check_f_class env;
      Lazy.force !fNNormal

    let mkPSubn env =
      check_f_class env;
      Lazy.force !fPSubn

    let mkNSubn env =
      check_f_class env;
      Lazy.force !fNSubn

    let mkPZero env =
      check_f_class env;
      Lazy.force !fPZero

    let mkNZero env =
      check_f_class env;
      Lazy.force !fNZero

    let mkPInf env =
      check_f_class env;
      Lazy.force !fPInf

    let mkNInf env =
      check_f_class env;
      Lazy.force !fNInf

    let mkNaN env =
      check_f_class env;
      Lazy.force !fNaN

    let mkArray env u t ty =
      check_array env;
      fc_mk_array u t ty

  end

module RNative = Primred.RedNative(RNativeEntries)

(** Callbacks *)

type value_of_result =
| VIrr
| VUndef
| VDef of constr * UVars.Instance.t * bool array
| VPrim of CPrimitives.t
| VSym of UVars.Instance.t * bool * machine_rewrite_rule list

let is_irrelevant evars r = match r with
| Sorts.Irrelevant -> true
| Sorts.RelevanceVar q -> evars.qvar_irrelevant q
| Sorts.Relevant -> false

exception Irrelevant

let value_of env evars flags tag (a : Obj.t) (b : Obj.t) =
  let shortcut_irrelevant r = if is_irrelevant evars r then raise Irrelevant in
  try match tag with
  | 2 ->
    let n : int = Obj.obj a in
    let d = Environ.lookup_rel n env in
    shortcut_irrelevant (RelDecl.get_relevance d);
    begin match d with
    | RelDecl.LocalAssum _ -> raise Not_found
    | RelDecl.LocalDef (_, t, _) -> VDef (Vars.lift n t, UVars.Instance.empty, [||])
    end
  | 1 ->
    let id : Id.t = Obj.obj a in
    let def = Environ.lookup_named id env in
    shortcut_irrelevant (Context.binder_relevance (NamedDecl.get_annot def));
    let ts = RedFlags.red_transparent flags in
    if TransparentState.is_transparent_variable ts id then
      match def with
      | NamedDecl.LocalDef (_, c, _) -> VDef (c, UVars.Instance.empty, [||])
      | NamedDecl.LocalAssum _ -> raise Not_found
    else raise Not_found
  | _ ->
    let cst : Constant.t = Obj.obj a in
    let u : UVars.Instance.t = Obj.obj b in
    let cb = CClosure.lookup_constant_handler env evars cst in
    shortcut_irrelevant (UVars.subst_instance_relevance u cb.const_relevance);
    let ts = RedFlags.red_transparent flags in
    if TransparentState.is_transparent_constant ts cst then match cb.const_body with
    | Undef _ | Def _ | OpaqueDef _ | Primitive _ ->
      let mask = match cb.const_body_code with
      | (Vmemitcodes.BCalias _ | Vmemitcodes.BCconstant | BCuncompiled) -> [||]
      | (Vmemitcodes.BCdefined (mask, _, _)) -> mask
      in
      begin match cb.const_body with
      | Def b -> VDef (b, u, mask)
      | OpaqueDef _ | Undef _ -> VUndef
      | Primitive p -> VPrim p
      | Symbol _ -> assert false
      end
    | Symbol b ->
      let r = match lookup_rewrite_rules cst env with
      | exception Not_found -> assert false
      | r -> r
      in
      VSym (u, b, r)
    else VUndef
  with
  | Irrelevant -> VIrr
  | Not_found -> VUndef

let eq k (a : Obj.t) (b : Obj.t) = match k with
| 0 -> Constant.CanOrd.equal (Obj.obj a) (Obj.obj b)
| 1 -> Ind.CanOrd.equal (Obj.obj a) (Obj.obj b)
| 2 -> Projection.Repr.CanOrd.equal (Obj.obj a) (Obj.obj b)
| 3 -> Evar.equal (Obj.obj a) (Obj.obj b)
| 4 -> CPrimitives.equal (Obj.obj a) (Obj.obj b)
| 5 -> Constant.UserOrd.equal (Obj.obj a) (Obj.obj b)
| 6 -> Ind.UserOrd.equal (Obj.obj a) (Obj.obj b)
| 7 -> Construct.UserOrd.equal (Obj.obj a) (Obj.obj b)
| 8 -> Projection.UserOrd.equal (Obj.obj a) (Obj.obj b)
| 9 -> Id.equal (Obj.obj a) (Obj.obj b)
| 10 -> Uint63.equal (Obj.obj a) (Obj.obj b)
| 11 -> Float64.equal (Obj.obj a) (Obj.obj b)
| 12 -> Pstring.equal (Obj.obj a) (Obj.obj b)
| 13 -> Sorts.equal (Obj.obj a) (Obj.obj b)
| _ -> assert false

let qeq env k (a : Obj.t) (b : Obj.t) = match k with
| 0 -> QInd.equal env (Obj.obj a) (Obj.obj b)
| 1 -> QConstruct.equal env (Obj.obj a) (Obj.obj b)
| 2 -> QConstant.equal env (Obj.obj a) (Obj.obj b)
| 3 -> QProjection.Repr.equal env (Obj.obj a) (Obj.obj b)
| _ -> assert false

let anomaly k =
  let msg = match k with
  | 0 -> "Uncaught pattern variable"
  | 1 -> "ill-typed term: found a match on a partially applied constructor."
  | 2 -> "conversion was given ill-typed terms (FLambda)."
  | 3 -> "conversion was given unreduced term (FLambda)."
  | 4 -> "conversion was given unreduced term (FConstruct)."
  | _ -> "Rust conversion"
  in
  CErrors.anomaly (Pp.str msg)

let lookup_mip env (ind : inductive) =
  let mib = Environ.lookup_mind (fst ind) env in
  mib, mib.mind_packets.(snd ind)

let ctor_ctx env ind i =
  let _, mip = lookup_mip env ind in
  let (ctx, _) = mip.mind_nf_lc.(i) in
  let ctx, _ = List.chop mip.mind_consnrealdecls.(i) ctx in
  List.map RelDecl.get_value ctx

let ctor_letctx env ind i =
  let _, mip = lookup_mip env ind in
  if Int.equal mip.mind_consnrealdecls.(i) mip.mind_consnrealargs.(i) then None
  else Some (ctor_ctx env ind i)

let arity_letctx env ind =
  let _, mip = lookup_mip env ind in
  if Int.equal mip.mind_nrealargs mip.mind_nrealdecls then None
  else
    let ctx, _ = List.chop mip.mind_nrealdecls mip.mind_arity_ctxt in
    Some (None :: List.map RelDecl.get_value ctx)

let inversion_indices env ind npar =
  let _, mip = lookup_mip env ind in
  let _, indargs = mip.mind_nf_lc.(0) in
  let _, allargs = destApp indargs in
  let _, branch_indices = Array.chop npar allargs in
  branch_indices

let eta_record env (ind : inductive) u =
  let mib = lookup_mind (fst ind) env in
  let specif = mib, mib.mind_packets.(snd ind) in
  if not (Declareops.is_record_with_eta specif u) then None
  else match Declareops.inductive_make_projections ind mib with
  | None -> assert false
  | Some projs ->
    let projs = Array.map (fun (p, r) -> (Projection.make p true, UVars.subst_instance_relevance u r)) projs in
    Some (mib.mind_nparams, projs)

let irr_flex env evars tag (a : Obj.t) (b : Obj.t) = match tag with
| 0 ->
  let con : Constant.t = Obj.obj a in
  let u : UVars.Instance.t = Obj.obj b in
  is_irrelevant evars @@ UVars.subst_instance_relevance u @@ Environ.constant_relevance con env
| 1 -> is_irrelevant evars @@ NamedDecl.get_relevance (Environ.lookup_named (Obj.obj a) env)
| _ -> is_irrelevant evars @@ RelDecl.get_relevance (Environ.lookup_rel (Obj.obj a) env)

let unfold_left env tag1 (a1 : Obj.t) tag2 (a2 : Obj.t) l2r =
  let oracle = Environ.oracle env in
  let to_er tag a = match tag with
  | 0 -> Some (Conv_oracle.EvalConstRef (Obj.obj a))
  | 1 -> Some (Conv_oracle.EvalVarRef (Obj.obj a))
  | _ -> None
  in
  let order = Conv_oracle.oracle_compare oracle (to_er tag1 a1) (to_er tag2 a2) in
  match order with
  | Conv_oracle.Left -> true
  | Conv_oracle.Right -> false
  | Conv_oracle.Same ->
    if (Environ.typing_flags env).unfold_dep_heuristic then
      if Int.equal tag1 0 && Int.equal tag2 0 then
        let cst1 = Obj.obj a1 and cst2 = Obj.obj a2 in
        if Environ.constant_depends_on env cst1 cst2 then true
        else if Environ.constant_depends_on env cst2 cst1 then false
        else l2r
      else l2r
    else if (Environ.typing_flags env).unfold_height_heuristic then
      if Int.equal tag1 0 && Int.equal tag2 0 then
        let cst1 = Obj.obj a1 and cst2 = Obj.obj a2 in
        if Environ.constant_higher_than env cst1 cst2 then true
        else if Environ.constant_higher_than env cst2 cst1 then false
        else l2r
      else l2r
    else l2r

let register () =
  let r = Callback.register in
  r "rconv_anomaly" anomaly;
  r "rconv_check_for_interrupt" (fun (_ : int) -> Control.check_for_interrupt ());
  r "rconv_eq" eq;
  r "rconv_qeq" qeq;
  r "rconv_constant_hash" Constant.UserOrd.hash;
  r "rconv_instance_equal" UVars.Instance.equal;
  r "rconv_subst_instance_instance" UVars.subst_instance_instance;
  r "rconv_subst_relevance" UVars.subst_instance_relevance;
  r "rconv_usubst_binder" (fun u x ->
      let open Context in
      let r = x.binder_relevance in
      let r' = UVars.subst_instance_relevance u r in
      if r == r' then x else { x with binder_relevance = r' });
  r "rconv_mk_sort_subst" (fun u t -> match kind t with
      | Sort s -> mkSort (UVars.subst_instance_sort u s)
      | _ -> assert false);
  r "rconv_sort_eq_under" (fun u1 s1 u2 s2 ->
      let subst_instance_sort u s =
        if UVars.Instance.is_empty u then s else UVars.subst_instance_sort u s
      in
      Sorts.equal (subst_instance_sort u1 s1) (subst_instance_sort u2 s2));
  r "rconv_qvar_irrelevant" (fun evars q -> evars.qvar_irrelevant q);
  r "rconv_ind_relevance" (fun env ind u ->
      UVars.subst_instance_relevance u @@ Environ.ind_relevance ind env);
  r "rconv_value_of" value_of;
  r "rconv_evar_expand" (fun evars ev -> evars.evar_expand ev);
  r "rconv_evar_irrelevant" (fun evars ev -> evars.evar_irrelevant ev);
  r "rconv_proj_make" (fun p -> Projection.make p true);
  r "rconv_unfold_projection" (fun flags p ->
      if RedFlags.red_projection flags p then Some (Projection.repr p) else None);
  r "rconv_prim_kind" CPrimitives.kind;
  r "rconv_prim_arity" CPrimitives.arity;
  r "rconv_red_prim" (fun env op u args -> RNative.red_prim env () op u args);
  r "rconv_parray_to_array" Parray.to_array;
  r "rconv_parray_of_array" Parray.of_array;
  r "rconv_parray_length" Parray.length_int;
  r "rconv_mind_params" (fun env (ind : inductive) ->
      let mib = Environ.lookup_mind (fst ind) env in
      List.map RelDecl.get_value mib.mind_params_ctxt);
  r "rconv_ctor_ctx" ctor_ctx;
  r "rconv_ctor_letctx" ctor_letctx;
  r "rconv_arity_letctx" arity_letctx;
  r "rconv_ind_nconstructors" (fun env ind ->
      let _, mip = lookup_mip env ind in Array.length mip.mind_nf_lc);
  r "rconv_inversion_indices" inversion_indices;
  r "rconv_eta_record" eta_record;
  r "rconv_irrelevant_variance" (fun u1 ->
      Array.make (snd (UVars.Instance.length u1)) UVars.Variance.Irrelevant);
  r "rconv_array_variance" (fun (_ : int) -> [|UVars.Variance.Irrelevant|]);
  r "rconv_all_transparent" (fun flags ->
      RedFlags.(red_add_transparent all (red_transparent flags)));
  r "rconv_std_flags" (fun (_ : int) -> (RedFlags.all, RedFlags.betaiotazeta, UVars.Instance.empty));
  r "rconv_share" (fun env -> (Environ.typing_flags env).Declarations.share_reduction);
  r "rconv_irr_maps" (fun env ->
      (Environ.Internal.has_irrelevant_constants env, Environ.Internal.has_irrelevant_inductives env));
  r "rconv_interrupt_ref" Control.interrupt;
  r "rconv_thread_delay_ref" Control.enable_thread_delay;
  r "rconv_conv_flex" (fun env flags cst ->
      evaluable_constant cst env && RedFlags.red_set flags (RedFlags.fCONST cst));
  r "rconv_is_array_type" (fun env cst -> is_array_type env cst);
  r "rconv_irr_flex" irr_flex;
  r "rconv_unfold_left" unfold_left;
  r "rconv_mk_lambda" (fun na ty c -> mkLambda (na, ty, c));
  r "rconv_ps_make" Partial_subst.make;
  r "rconv_ps_add_term" (fun i depth (h : fhandle) subst -> Partial_subst.add_term i (depth, h) subst);
  r "rconv_ps_finalize" (fun subst ->
      let ts, qs, us = Partial_subst.to_arrays subst in
      (ts, UVars.Instance.of_array (qs, us)));
  r "rconv_instance_pattern_match" UVars.Instance.pattern_match;
  r "rconv_sort_pattern_match" (fun ps t subst -> match kind t with
      | Sort s -> Sorts.pattern_match ps s subst
      | _ -> assert false);
  r "rconv_result_ok" (fun s -> Result.Ok s);
  r "rconv_result_error" (fun b e -> Result.Error (if b then Some e else None))

let check_layout () =
  let open Names in
  let id = Id.of_string "x" in
  let na = Context.annotR (Name id) in
  let c = mkProp in
  let samples = [
    0, mkRel 1; 1, mkVar id; 2, mkMeta 0; 4, c; 5, mkCast (c, DEFAULTcast, c);
    6, mkProd (na, c, c); 7, mkLambda (na, c, c); 8, mkLetIn (na, c, c, c);
    9, mkApp (c, [|c|]); 17, mkInt Uint63.zero; 18, mkFloat (Float64.of_float 0.);
  ] in
  List.iter (fun (n, c) ->
      if not (Int.equal (constr_tag c) n) then
        CErrors.anomaly Pp.(str "Rust conversion: unexpected constr layout."))
    samples

let initialized = ref false

let init () =
  if not !initialized then begin
    setup ();
    register ();
    check_layout ();
    initialized := true
  end

let conv ~typed reds (cv_pb : int) l2r evars env graph state check t1 t2 =
  let () = init () in
  let args = (typed, reds, cv_pb, l2r, evars, env, graph, state, check, t1, t2) in
  Obj.obj (conv_raw (Obj.repr args))
