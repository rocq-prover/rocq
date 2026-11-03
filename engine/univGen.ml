(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Sorts
open Names
open Constr
open Univ
open UVars

module QualityOrSet = struct
  type t = Qual of Quality.t | Set

  let equal a b = match a, b with
    | Qual a, Qual b -> Quality.equal a b
    | Set, Set -> true
    | Qual _, Set | Set, Qual _ -> false

  let compare a b = match a, b with
    | Qual a, Qual b -> Quality.compare a b
    | Set, Set -> 0
    | Qual _, Set -> 1
    | Set, Qual _ -> -1

  let eliminates_to a b =
    match a, b with
    | Set, Qual (QConstant QType) -> false
    | _ ->
      let to_qual = function
        | Set -> Quality.qtype
        | Qual q -> q
      in Inductive.raw_eliminates_to (to_qual a) (to_qual b)

  let of_quality q = Qual q
  let of_sort s = match s with
    | Sorts.Set -> Set
    | s -> of_quality (Sorts.quality s)
  let quality q = match q with
    | Set -> Quality.qtype
    | Qual q -> q

  let set = Set

  let qtype = Qual Quality.qtype
  let prop = Qual Quality.qprop
  let sprop = Qual Quality.qsprop

  let is_type q = match q with
    | Set -> false
    | Qual q -> Quality.is_qtype q

  let is_set q = match q with
    | Set -> true
    | Qual _ -> false

  let is_prop q = match q with
    | Set -> false
    | Qual q -> Quality.is_qprop q

  let is_sprop q = match q with
    | Set -> false
    | Qual q -> Quality.is_qsprop q

  let pr prv q = match q with
    | Set -> Pp.str"Set"
    | Qual q -> Quality.pr prv q

  let raw_pr = pr Sorts.Quality.raw_printer

  let all_constants = Set :: List.map (fun q -> Qual q) Quality.all_constants
end

type sort_context_set = (QVar.Set.t * Univ.Level.Set.t) * PConstraints.t

type 'a in_sort_context_set = 'a * sort_context_set

let empty_sort_context = (QVar.Set.empty, Level.Set.empty), PConstraints.empty

let is_empty_sort_context ((qs,us),csts) =
  QVar.Set.is_empty qs && Level.Set.is_empty us && PConstraints.is_empty csts

let sort_context_union ((qs,us),csts) ((qs',us'),csts') =
  ((QVar.Set.union qs qs', Level.Set.union us us'), PConstraints.union csts csts')

let diff_sort_context ((qs,us),csts) ((qs',us'),csts') =
  (QVar.Set.diff qs qs', Level.Set.diff us us'), PConstraints.diff csts csts'

let pr_sort_context printer ((vs, us), cst as ctx) =
  let open Pp in
  if is_empty_sort_context ctx then mt ()
  else
    let vs =
      if Sorts.QVar.Set.is_empty vs then mt ()
      else Sorts.QVar.Set.pr printer.Sorts.prq.prvar vs ++ pr_semicolon ()
    in
    hov 0 (h (vs ++ Level.Set.pr printer.pru us ++ str " |") ++ brk(1,2) ++ h (PConstraints.pr printer cst))

type univ_length_mismatch = {
  gref : GlobRef.t;
  actual : int * int;
  expect : int * int;
}
(* Due to an OCaml bug ocaml/ocaml#10027 inlining this record will cause
compliation with -rectypes to crash. *)
exception UniverseLengthMismatch of univ_length_mismatch

let () = CErrors.register_handler (function
    | UniverseLengthMismatch { gref; actual=(aq,au); expect=(eq,eu) } ->
      let ppreal, ppexpected =
        if aq = 0 && eq = 0 then Pp.(int au, int eu)
        else Pp.(str "(" ++ int aq ++ str " | " ++ int au ++ str ")"
                , str "(" ++ int eq ++ str " | " ++ int eu ++ str ")")
      in
      Some Pp.(str "Universe instance length for " ++ Nametab.pr_global_env Id.Set.empty gref ++
               spc() ++ str "is " ++ ppreal ++
               spc() ++ str "but should be " ++ ppexpected ++ str".")
  | _ -> None)

(* Generator of levels *)
let new_univ_id =
  let cnt = ref 0 in
  fun () -> incr cnt; !cnt

let new_univ_global () =
  let s = if Flags.async_proofs_is_worker() then !Flags.async_proofs_worker_id else "" in
  Univ.UGlobal.make (Global.current_dirpath ()) s (new_univ_id ())

module Supply =
struct
  (* Next indices of the unification levels and sort variables *)
  type t = { level : int; sort : int }

  let empty = { level = 1; sort = 1 }

  let process () =
    if Flags.async_proofs_is_worker() then !Flags.async_proofs_worker_id else ""

  let fresh_level s = { s with level = s.level + 1 }, Level.make_unif (process ()) s.level

  let fresh_qvar s = { s with sort = s.sort + 1 }, QVar.make_unif (process ()) s.sort

  let union s s' =
    { level = max s.level s'.level; sort = max s.sort s'.sort }

  let add_level l s = match Level.unif_repr l with
    | Some (_, n) when n >= s.level -> { s with level = n + 1 }
    | Some _ | None -> s

  let add_qvar q s = match QVar.repr q with
    | Unif (_, n) when n >= s.sort -> { s with sort = n + 1 }
    | Unif _ | Var _ | Secvar _ -> s

  let add_levels ls s = Level.Set.fold add_level ls s

  let add_qvars qs s = QVar.Set.fold add_qvar qs s
end

let globalize_context_set ?(subst = Level.Map.empty) (ls, csts) =
  let add l subst =
    if Level.is_unif l && not (Level.Map.mem l subst) then
      Level.Map.add l (Level.make (new_univ_global ())) subst
    else subst
  in
  let subst = Level.Set.fold add (UnivConstraints.levels ~init:ls csts) subst in
  let ls = Level.Set.fold (fun l acc -> Level.Set.add (subst_univs_level_level subst l) acc)
      ls Level.Set.empty
  in
  (ls, subst_univs_constraints subst csts), subst

let globalize_section_context ?(subst = Level.Map.empty) uctx =
  let qs, us = Instance.to_array (UContext.instance uctx) in
  let qcst, ucst = UContext.constraints uctx in
  let levels = Array.fold_right Level.Set.add us Level.Set.empty in
  let (_, ucst), subst = globalize_context_set ~subst (levels, ucst) in
  let us = Array.map (subst_univs_level_level subst) us in
  UContext.make (UContext.names uctx) (Instance.of_array (qs, us), (qcst, ucst)), subst

let fresh_instance supply auctx : _ * _ in_sort_context_set =
  let qlen, ulen = AbstractContext.size auctx in
  let supply, qinst = Array.fold_left_map (fun s () -> Supply.fresh_qvar s) supply (Array.make qlen ()) in
  let supply, uinst = Array.fold_left_map (fun s () -> Supply.fresh_level s) supply (Array.make ulen ()) in
  let qctx = Array.fold_right QVar.Set.add qinst QVar.Set.empty in
  let uctx = Array.fold_right Level.Set.add uinst Level.Set.empty in
  let inst = Instance.of_array (Array.map (fun q -> Sorts.Quality.QVar q) qinst, uinst) in
  supply, (inst, ((qctx,uctx), AbstractContext.instantiate inst auctx))

let existing_instance ?loc ~gref auctx inst =
  let () =
    let actual = Instance.length inst
    and expect = AbstractContext.size auctx in
      if not (UVars.eq_sizes actual expect) then
        Loc.raise ?loc (UniverseLengthMismatch { gref; actual; expect })
      else ()
  in
  inst, ((Sorts.QVar.Set.empty,Level.Set.empty), AbstractContext.instantiate inst auctx)

let fresh_instance_from ?loc supply ctx = function
  | Some (gref,inst) -> supply, existing_instance ?loc ~gref ctx inst
  | None -> fresh_instance supply ctx

(** Fresh universe polymorphic construction *)

let fresh_global_instance ?loc ?names supply env gr =
  let auctx = Environ.universes_of_global env gr in
  let names = Option.map (fun x -> gr, x) names in
  fresh_instance_from ?loc supply auctx names

let fresh_constant_instance supply env c =
  let supply, (u, ctx) = fresh_global_instance supply env (GlobRef.ConstRef c) in
  supply, ((c, u), ctx)

let fresh_inductive_instance supply env ind =
  let supply, (u, ctx) = fresh_global_instance supply env (GlobRef.IndRef ind) in
  supply, ((ind, u), ctx)

let fresh_constructor_instance supply env c =
  let supply, (u, ctx) = fresh_global_instance supply env (GlobRef.ConstructRef c) in
  supply, ((c, u), ctx)

let fresh_array_instance supply env =
  let auctx = CPrimitives.typ_univs CPrimitives.PT_array in
  fresh_instance_from supply auctx None

let fresh_global_instance ?loc ?names supply env gr =
  let supply, (u, ctx) = fresh_global_instance ?loc ?names supply env gr in
  supply, (mkRef (gr, u), ctx)

let constr_of_monomorphic_global env gr =
  if not (Environ.is_polymorphic env gr) then
    fst (snd (fresh_global_instance Supply.empty env gr))
  else CErrors.user_err
      Pp.(str "globalization of polymorphic reference " ++ Nametab.pr_global_env Id.Set.empty gr ++
          str " would forget universes.")

let fresh_sort_in_quality supply =
  let open QualityOrSet in
  function
  | Qual (QConstant QSProp) -> supply, (Sorts.sprop, empty_sort_context)
  | Qual (QConstant QProp) -> supply, (Sorts.prop, empty_sort_context)
  | Set -> supply, (Sorts.set, empty_sort_context)
  | Qual (QGlobal _ as q) ->
    let supply, u = Supply.fresh_level supply in
    supply, (Sorts.make q (Univ.Universe.make u), ((QVar.Set.empty,Level.Set.singleton u), PConstraints.empty))
  | Qual (QConstant QType | QVar _ (* Treat as Type *)) ->
    let supply, u = Supply.fresh_level supply in
    supply, (sort_of_univ (Univ.Universe.make u), ((QVar.Set.empty,Level.Set.singleton u), PConstraints.empty))

let fresh_sort_context_instance supply ((qs, us), csts) =
  let ufold u (supply, us, usubst) =
    let supply, u' = Supply.fresh_level supply in
    (supply, Level.Set.add u' us, Level.Map.add u u' usubst)
  in
  let qfold q (supply, qs, qsubst) =
    let supply, q' = Supply.fresh_qvar supply in
    supply, QVar.Set.add q' qs, QVar.Map.add q (Sorts.Quality.QVar q') qsubst
  in
  let supply, us, usubst = Level.Set.fold ufold us (supply, Level.Set.empty, Level.Map.empty) in
  let supply, qs, qsubst = QVar.Set.fold qfold qs (supply, QVar.Set.empty, QVar.Map.empty) in
  let csts = subst_poly_constraints (qsubst, usubst) csts in
  supply, ((qsubst, usubst), ((qs, us), csts))
