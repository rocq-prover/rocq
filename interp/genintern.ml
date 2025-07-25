(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Genarg

module Store = Store.Make ()

type ntnvar_status = {
  mutable ntnvar_used : bool list;
  mutable ntnvar_used_as_binder : bool;
  mutable ntnvar_scopes : Notation_term.subscopes option;
  mutable ntnvar_binding_ids : Notation_term.notation_var_binders option;
  ntnvar_typ : Notation_term.notation_var_internalization_type;
}

type intern_variable_status = {
  intern_ids : Id.Set.t;
  notation_variable_status : ntnvar_status Id.Map.t;
}

type glob_sign = {
  ltacvars : Id.Set.t;
  genv : Environ.env;
  extra : Store.t;
  intern_sign : intern_variable_status;
  strict_check : bool;
}

let empty_intern_sign = {
  intern_ids = Id.Set.empty;
  notation_variable_status = Id.Map.empty;
}

let empty_glob_sign ~strict env = {
  ltacvars = Id.Set.empty;
  genv = env;
  extra = Store.empty;
  intern_sign = empty_intern_sign;
  strict_check = strict;
}

(** In globalize tactics, we need to keep the initial [constr_expr] to recompute
   in the environment by the effective calls to Intro, Inversion, etc
   The [constr_expr] field is [None] in TacDef though *)
type glob_constr_and_expr = Glob_term.glob_constr * Constrexpr.constr_expr option
type glob_constr_pattern_and_expr = Id.Set.t * glob_constr_and_expr * Pattern.uninstantiated_pattern

type ('raw, 'glb) intern_fun = glob_sign -> 'raw -> glob_sign * 'glb
type 'glb ntn_subst_fun = ntnvar_status Id.Map.t -> (Id.t -> Glob_term.glob_constr option) -> 'glb -> 'glb

module InternObj =
struct
  type ('raw, 'glb, 'top) obj = ('raw, 'glb) intern_fun
  let name = "intern"
  let default _ = None
end

module NtnSubstObj =
struct
  type ('raw, 'glb, 'top) obj = 'glb ntn_subst_fun
  let name = "notation_subst"
  let default _ = None
end

module Intern = Register (InternObj)
module NtnSubst = Register (NtnSubstObj)

let intern = Intern.obj
let register_intern0 = Intern.register0

let generic_intern ist (GenArg (Rawwit wit, v)) =
  let (ist, v) = intern wit ist v in
  (ist, in_gen (glbwit wit) v)

type ('raw,'glb) intern_pat_fun = ?loc:Loc.t -> ('raw,'glb) intern_fun

module InternPatObj = struct
  type ('raw, 'glb, 'top) obj = ('raw, 'glb) intern_pat_fun
  let name = "intern_pat"
  let default tag =
    Some (fun ?loc ->
        let name = Genarg.(ArgT.repr tag) in
        CErrors.user_err ?loc Pp.(str "This quotation is not supported in tactic patterns (" ++ str name ++ str ")"))
end

module InternPat = Register (InternPatObj)

let intern_pat = InternPat.obj

let register_intern_pat = InternPat.register0

let generic_intern_pat ?loc ist (GenArg (Rawwit wit, v)) =
  let (ist, v) = intern_pat wit ?loc ist v in
  (ist, in_gen (glbwit wit) v)

(** Notation substitution *)

let substitute_notation = NtnSubst.obj
let register_ntn_subst0 = NtnSubst.register0

let generic_substitute_notation avoid env (GenArg (Glbwit wit, v) as orig) =
  let v' = substitute_notation wit avoid env v in
  if v' == v then orig else in_gen (glbwit wit) v'

let with_used_ntnvars ntnvars f =
  let () = Id.Map.iter (fun _ status ->
      status.ntnvar_used <- false:: status.ntnvar_used)
      ntnvars
  in
  match f () with
  | v ->
    let used = Id.Map.fold (fun id status acc -> match status.ntnvar_used with
        | [] -> assert false
        | false :: rest -> status.ntnvar_used <- rest; acc
        | true :: rest ->
          let rest = match rest with
            | [] | true :: _ -> rest
            | false :: rest -> true :: rest
          in
          status.ntnvar_used <- rest;
          Id.Set.add id acc)
        ntnvars
        Id.Set.empty
    in
    used, v
  | exception e ->
    let e = Exninfo.capture e in
    let () = Id.Map.iter (fun _ status -> status.ntnvar_used <- List.tl status.ntnvar_used) ntnvars in
    Exninfo.iraise e
