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
open Tac2expr
open Mod_subst

let subst_or_tuple f subst o = match o with
| Tuple _ -> o
| Other v ->
  let v' = f subst v in
  if v' == v then o else Other v'

let rec subst_type subst t = match t with
| GTypVar _ -> t
| GTypArrow (t1, t2) ->
  let t1' = subst_type subst t1 in
  let t2' = subst_type subst t2 in
  if t1' == t1 && t2' == t2 then t
  else GTypArrow (t1', t2')
| GTypRef (kn, tl) ->
  let kn' = subst_or_tuple subst_kn subst kn in
  let tl' = List.Smart.map (fun t -> subst_type subst t) tl in
  if kn' == kn && tl' == tl then t else GTypRef (kn', tl')

let rec subst_glb_pat subst = function
  | (GPatVar _ | GPatAtm _) as pat0 -> pat0
  | GPatRef (ctor,pats) as pat0 ->
    let ctor' =
      let ctyp' = Option.Smart.map (subst_kn subst) ctor.ctyp in
      if ctyp' == ctor.ctyp then ctor
      else {ctor with ctyp = ctyp'}
    in
    let pats' = List.Smart.map (subst_glb_pat subst) pats in
    if ctor' == ctor && pats' == pats then pat0
    else GPatRef (ctor', pats')
  | GPatOr pats as pat0 ->
    let pats' = List.Smart.map (subst_glb_pat subst) pats in
    if pats' == pats then pat0
    else GPatOr pats'
  | GPatAs (p,x) as pat0 ->
    let p' = subst_glb_pat subst p in
    if p' == p then pat0
    else GPatAs (p',x)

let rec subst_expr subst e = match e with
| GTacAtm _ | GTacVar _ | GTacPrm _ -> e
| GTacRef kn -> GTacRef (subst_kn subst kn)
| GTacFun (ids, e) -> GTacFun (ids, subst_expr subst e)
| GTacApp (f, args) ->
  GTacApp (subst_expr subst f, List.map (fun e -> subst_expr subst e) args)
| GTacLet (r, bs, e) ->
  let bs = List.map (fun (na, e) -> (na, subst_expr subst e)) bs in
  GTacLet (r, bs, subst_expr subst e)
| GTacCst (t, n, el) as e0 ->
  let t' = subst_or_tuple subst_kn subst t in
  let el' = List.Smart.map (fun e -> subst_expr subst e) el in
  if t' == t && el' == el then e0 else GTacCst (t', n, el')
| GTacCse (e, ci, cse0, cse1) ->
  let cse0' = Array.map (fun e -> subst_expr subst e) cse0 in
  let cse1' = Array.map (fun (ids, e) -> (ids, subst_expr subst e)) cse1 in
  let ci' = subst_or_tuple subst_kn subst ci in
  GTacCse (subst_expr subst e, ci', cse0', cse1')
| GTacWth { opn_match = e; opn_branch = br; opn_default = (na, def) } as e0 ->
  let e' = subst_expr subst e in
  let def' = subst_expr subst def in
  let fold kn (self, vars, p) accu =
    let kn' = subst_kn subst kn in
    let p' = subst_expr subst p in
    if kn' == kn && p' == p then accu
    else KerName.Map.add kn' (self, vars, p') (KerName.Map.remove kn accu)
  in
  let br' = KerName.Map.fold fold br br in
  if e' == e && br' == br && def' == def then e0
  else GTacWth { opn_match = e'; opn_default = (na, def'); opn_branch = br' }
| GTacFullMatch (e,brs) as e0 ->
  let e' = subst_expr subst e in
  let brs' = List.Smart.map (fun (pat,br as pbr) ->
      let pat' = subst_glb_pat subst pat in
      let br' = subst_expr subst br in
      if pat' == pat && br' == br then pbr
      else (pat',br'))
      brs
  in
  if e' == e && brs' == brs then e0
  else GTacFullMatch (e', brs')
| GTacPrj (kn, e, p) as e0 ->
  let kn' = subst_kn subst kn in
  let e' = subst_expr subst e in
  if kn' == kn && e' == e then e0 else GTacPrj (kn', e', p)
| GTacSet (kn, e, p, r) as e0 ->
  let kn' = subst_kn subst kn in
  let e' = subst_expr subst e in
  let r' = subst_expr subst r in
  if kn' == kn && e' == e && r' == r then e0 else GTacSet (kn', e', p, r')
| GTacExt (tag, arg) ->
  let tpe = Tac2env.interp_ml_object tag in
  let arg' = tpe.ml_subst subst arg in
  if arg' == arg then e else GTacExt (tag, arg')
| GTacOpn (kn, el) as e0 ->
  let kn' = subst_kn subst kn in
  let el' = List.Smart.map (fun e -> subst_expr subst e) el in
  if kn' == kn && el' == el then e0 else GTacOpn (kn', el')

let subst_typedef subst e = match e with
| GTydDef t ->
  let t' = Option.Smart.map (fun t -> subst_type subst t) t in
  if t' == t then e else GTydDef t'
| GTydAlg galg ->
  let map (warn, c, tl as p) =
    let tl' = List.Smart.map (fun t -> subst_type subst t) tl in
    if tl' == tl then p else (warn, c, tl')
  in
  let constrs' = List.Smart.map map galg.galg_constructors in
  if constrs' == galg.galg_constructors then e
  else GTydAlg { galg with galg_constructors = constrs' }
| GTydRec fields ->
  let map (c, mut, t as p) =
    let t' = subst_type subst t in
    if t' == t then p else (c, mut, t')
  in
  let fields' = List.Smart.map map fields in
  if fields' == fields then e else GTydRec fields'
| GTydOpn -> GTydOpn

let subst_quant_typedef subst (prm, def as qdef) =
  let def' = subst_typedef subst def in
  if def' == def then qdef else (prm, def')

let subst_type_scheme subst (prm, t as sch) =
  let t' = subst_type subst t in
  if t' == t then sch else (prm, t')

let subst_or_relid subst ref = match ref with
| RelId _ -> ref
| AbsKn kn ->
  let kn' = subst_or_tuple subst_kn subst kn in
  if kn' == kn then ref else AbsKn kn'

let rec subst_rawtype subst ({CAst.loc;v=tr} as t) = match tr with
| CTypVar _ -> t
| CTypArrow (t1, t2) ->
  let t1' = subst_rawtype subst t1 in
  let t2' = subst_rawtype subst t2 in
  if t1' == t1 && t2' == t2 then t else CAst.make ?loc @@ CTypArrow (t1', t2')
| CTypRef (ref, tl) ->
  let ref' = subst_or_relid subst ref in
  let tl' = List.Smart.map (fun t -> subst_rawtype subst t) tl in
  if ref' == ref && tl' == tl then t else CAst.make ?loc @@ CTypRef (ref', tl')

let subst_tacref subst ref = match ref with
| RelId _ -> ref
| AbsKn (TacConstant kn) ->
  let kn' = subst_kn subst kn in
  if kn' == kn then ref else AbsKn (TacConstant kn')
| AbsKn (TacAlias kn) ->
  let kn' = subst_kn subst kn in
  if kn' == kn then ref else AbsKn (TacAlias kn')

let subst_projection subst prj = match prj with
| RelId _ -> prj
| AbsKn kn ->
  let kn' = subst_kn subst kn in
  if kn' == kn then prj else AbsKn kn'

let rec subst_rawpattern subst ({CAst.loc;v=pr} as p) = match pr with
| CPatVar _ | CPatAtm _ -> p
| CPatRef (c, pl) ->
  let pl' = List.Smart.map (fun p -> subst_rawpattern subst p) pl in
  let c' = subst_or_relid subst c in
  if pl' == pl && c' == c then p else CAst.make ?loc @@ CPatRef (c', pl')
| CPatCnv (pat, ty) ->
  let pat' = subst_rawpattern subst pat in
  let ty' = subst_rawtype subst ty in
  if pat' == pat && ty' == ty then p else CAst.make ?loc @@ CPatCnv (pat', ty')
| CPatOr pl ->
  let pl' = List.Smart.map (fun p -> subst_rawpattern subst p) pl in
  if pl' == pl then p else CAst.make ?loc @@ CPatOr pl'
| CPatAs (pat,x) ->
  let pat' = subst_rawpattern subst pat in
  if pat' == pat then p else CAst.make ?loc @@ CPatAs (pat', x)
| CPatRecord el ->
  let map (prj, e as p) =
    let prj' = subst_projection subst prj in
    let e' = subst_rawpattern subst e in
    if prj' == prj && e' == e then p else (prj', e')
  in
  let el' = List.Smart.map map el in
  if el' == el then p else CAst.make ?loc @@ CPatRecord el'

(** Used for notations *)
let rec subst_rawexpr subst ({CAst.loc;v=tr} as t) = match tr with
| CTacAtm _ -> t
| CTacRef ref ->
  let ref' = subst_tacref subst ref in
  if ref' == ref then t else CAst.make ?loc @@ CTacRef ref'
| CTacCst ref ->
  let ref' = subst_or_relid subst ref in
  if ref' == ref then t else CAst.make ?loc @@ CTacCst ref'
| CTacFun (bnd, e) ->
  let map pat = subst_rawpattern subst pat in
  let bnd' = List.Smart.map map bnd in
  let e' = subst_rawexpr subst e in
  if bnd' == bnd && e' == e then t else CAst.make ?loc @@ CTacFun (bnd', e')
| CTacApp (e, el) ->
  let e' = subst_rawexpr subst e in
  let el' = List.Smart.map (fun e -> subst_rawexpr subst e) el in
  if e' == e && el' == el then t else CAst.make ?loc @@ CTacApp (e', el')
| CTacLet (isrec, bnd, e) ->
  let map (na, e as p) =
    let na' = subst_rawpattern subst na in
    let e' = subst_rawexpr subst e in
    if na' == na && e' == e then p else (na', e')
  in
  let bnd' = List.Smart.map map bnd in
  let e' = subst_rawexpr subst e in
  if bnd' == bnd && e' == e then t else CAst.make ?loc @@ CTacLet (isrec, bnd', e')
| CTacCnv (e, c) ->
  let e' = subst_rawexpr subst e in
  let c' = subst_rawtype subst c in
  if c' == c && e' == e then t else CAst.make ?loc @@ CTacCnv (e', c')
| CTacSeq (e1, e2) ->
  let e1' = subst_rawexpr subst e1 in
  let e2' = subst_rawexpr subst e2 in
  if e1' == e1 && e2' == e2 then t else CAst.make ?loc @@ CTacSeq (e1', e2')
| CTacIft (e, e1, e2) ->
  let e' = subst_rawexpr subst e in
  let e1' = subst_rawexpr subst e1 in
  let e2' = subst_rawexpr subst e2 in
  if e' == e && e1' == e1 && e2' == e2 then t else CAst.make ?loc @@ CTacIft (e', e1', e2')
| CTacCse (e, bl) ->
  let map (p, e as x) =
    let p' = subst_rawpattern subst p in
    let e' = subst_rawexpr subst e in
    if p' == p && e' == e then x else (p', e')
  in
  let e' = subst_rawexpr subst e in
  let bl' = List.Smart.map map bl in
  if e' == e && bl' == bl then t else CAst.make ?loc @@ CTacCse (e', bl')
| CTacRec (def, el) ->
  let def' = Option.Smart.map (subst_rawexpr subst) def in
  let map (prj, e as p) =
    let prj' = subst_projection subst prj in
    let e' = subst_rawexpr subst e in
    if prj' == prj && e' == e then p else (prj', e')
  in
  let el' = List.Smart.map map el in
  if def' == def && el' == el then t else CAst.make ?loc @@ CTacRec (def',el')
| CTacPrj (e, prj) ->
    let prj' = subst_projection subst prj in
    let e' = subst_rawexpr subst e in
    if prj' == prj && e' == e then t else CAst.make ?loc @@ CTacPrj (e', prj')
| CTacSet (e, prj, r) ->
    let prj' = subst_projection subst prj in
    let e' = subst_rawexpr subst e in
    let r' = subst_rawexpr subst r in
    if prj' == prj && e' == e && r' == r then t else CAst.make ?loc @@ CTacSet (e', prj', r')
| CTacGlb (prms, args, body, ty) ->
  let args' = List.Smart.map (fun (na, arg, ty as o) ->
      let arg' = subst_rawexpr subst arg in
      let ty' = Option.Smart.map (subst_type subst) ty in
      if arg' == arg && ty' == ty then o
      else (na, arg', ty'))
      args
  in
  let body' = subst_expr subst body in
  let ty' = subst_type subst ty in
  if args' == args && body' == body && ty' == ty then t
  else CAst.make ?loc @@ CTacGlb (prms, args', body', ty')
| CTacSyn _ | CTacExt _ -> assert false (** Should not be generated by globalization *)

let () = Gensubst.register_constr_subst Tac2env.wit_ltac2_constr (fun s (ids, e) -> ids, subst_expr s e)
let () = Gentactic.register_subst Tac2env.wit_ltac2_tac subst_expr
