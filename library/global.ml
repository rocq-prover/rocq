(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Util
open Names
open Term
open Instantiate
open Sign
open Environ
open Safe_env
open Summary

(* We introduce here the global environment of the system, and we declare it
   as a synchronized table. *)

let global_env = ref empty_environment

let safe_env () = !global_env

let env () = env_of_safe_env !global_env

let _ = 
  declare_global_environment
    { freeze_function = (fun () -> !global_env);
      unfreeze_function = (fun fr -> global_env := fr);
      init_function = (fun () -> global_env := empty_environment);
      survive_section = false }

(* Then we export the functions of [Typing] on that environment. *)

let universes () = universes (env ())
(*let context () = context (env ())*)
let named_context () = named_context (env ())

let push_named_def idc = global_env := push_named_def idc !global_env
let push_named_assum idc = global_env := push_named_assum idc !global_env

let update_env f = 
  let env',res = f !global_env in
    global_env:=env';
    res

let add_constant l ce = update_env (add_constant l ce)
(*let add_discharged_constant sp r l = 
  global_env := add_discharged_constant sp r l !global_env *)
let add_mind mie = update_env (add_mind mie)

let add_module l me = update_env (add_module l me) 

let add_modtype l mte = update_env (add_modtype l mte)

(*let add_constraints c = global_env := add_constraints c !global_env*)

(*let pop_named_decls ids = global_env := pop_named_decls ids !global_env*)

let lookup_named id = lookup_named id !global_env
let lookup_constant ln = lookup_constant ln !global_env
let lookup_mind ln = lookup_mind ln !global_env
let lookup_mind_specif c = lookup_mind_specif c !global_env

let lookup_module mp = lookup_module mp !global_env
let lookup_modtype ln = lookup_modtype ln !global_env

let begin_module l params result = 
  global_env := begin_module l params result !global_env
let end_module l = update_env (end_module l)
let begin_modtype l params = 
  global_env := begin_modtype l params !global_env
let end_modtype l = update_env (end_modtype l)
let current_modpath () = current_modpath !global_env
let current_msid () = current_msid !global_env

let set_opaque sp = set_opaque !global_env sp
let set_transparent sp = set_transparent !global_env sp

let export s = export !global_env s
let import cenv digest = update_env (import cenv digest)

(* Some instanciations of functions from [Environ]. *)
(*
let sp_of_global ref = Environ.sp_of_global (env_of_safe_env !global_env) ref

(* To know how qualified a name should be to be understood in the current env*)

let qualid_of_global ref =  
  let sp = sp_of_global ref in
  let id = basename sp in
  let rec find_visible dir qdir =
    let qid = Nametab.make_qualid qdir id in
    if (try Nametab.locate qid = ref with Not_found -> false) then qid
    else match dir with
      | [] -> Nametab.qualid_of_sp sp
      | a::l -> find_visible l (a::qdir)
  in
  find_visible (List.rev (dirpath sp)) []

let string_of_global ref = Nametab.string_of_qualid (qualid_of_global ref)
*)
(*s Function to get an environment from the constants part of the global
    environment and a given context. *)

let env_of_context hyps = 
  change_hyps (fun _ -> hyps) (env_of_safe_env !global_env)

(* Functions of [Inductive], composed with [lookup_mind_specif]. *)
(* Rem:Cannot open Inductive to avoid clash with Inductive.lookup_mind_specif*)

let mind_is_recursive =
  Util.compose Inductive.mis_is_recursive lookup_mind_specif 

let mind_nconstr = Util.compose Inductive.mis_nconstr lookup_mind_specif
let mind_nparams = Util.compose Inductive.mis_nparams lookup_mind_specif
let mind_nf_lc = Util.compose Inductive.mis_nf_lc lookup_mind_specif


