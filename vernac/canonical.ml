(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
open Libobject
open Structures

let open_canonical_structure (o,_) _sum =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  Instance.register env sigma ~warn:false o

let cache_canonical_structure (o,_) _sum =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  Instance.register ~warn:true env sigma o

let discharge_canonical_structure _sum (x, local) =
  let gref = Instance.repr x in
  if local || (Globnames.isVarRef gref && Global.is_in_section gref) then None
  else Some (x, local)

let canon_cat = create_category "canonicals"

let inCanonStruc : Instance.t * bool -> obj =
  Interp.declare_object
    {(default_object "CANONICAL-STRUCTURE") with
     open_function = simple_open ~cat:canon_cat open_canonical_structure;
     cache_function = cache_canonical_structure;
     subst_function = (fun _sum subst (c,local) -> Instance.subst subst c, local);
     classify_function = (fun x -> Substitute);
     discharge_function = discharge_canonical_structure }

let add_canonical_structure sum x = Lib.Interp.add_leaf sum (inCanonStruc x)

let declare_canonical_structure sum ?(local=false) ref =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  add_canonical_structure sum (Instance.make env sigma ref, local)
