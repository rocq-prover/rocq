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
open Declarations
open Environ

module RelDecl = Context.Rel.Declaration

let relevance_of_rel env n =
  let decl = lookup_rel n env in
  RelDecl.get_relevance decl

let relevance_of_var env x =
  let decl = lookup_named x env in
  Context.Named.Declaration.get_relevance decl

let relevance_of_constant env (c,u) =
  let decl = lookup_constant c env in
  UVars.subst_instance_relevance u decl.const_relevance

let relevance_of_constructor env ((ind,_),u) =
  Inductive.relevance_of_inductive env (ind,u)

let relevance_of_projection_repr env (p, u) =
  let mib = lookup_mind (Names.Projection.Repr.mind p) env in
  let _mind,i = Names.Projection.Repr.inductive p in
  match mib.mind_packets.(i).mind_record with
  | NotRecord | FakeRecord ->
    CErrors.anomaly ~label:"relevance_of_projection" Pp.(str "not a projection")
  | PrimRecord { relevances; _ }->
    UVars.subst_instance_relevance u relevances.(Names.Projection.Repr.arg p)

let relevance_of_projection env (p,u) =
  relevance_of_projection_repr env (Names.Projection.repr p,u)

let relevance_of_term env c =
  (* Inferring the type, rather than following the operand/head, also handles
     indirect sort changes through unsafe casts in types and function types.
     Callers with a checked type judgment should use its sort directly. *)
  let j = Typeops.infer env c in
  let tj = Typeops.infer_type env j.uj_type in
  Sorts.relevance_of_sort tj.utj_type
