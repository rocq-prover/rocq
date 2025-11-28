(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Univ
open Sorts

type t = ElimConstraints.t * UnivConstraints.t

type pconstraints = t

let make q u = (q, u)

let qualities = fst

let univs = snd

let add_quality q (qc, lc) = (ElimConstraints.add q qc, lc)

let add_univ u (qc, lc) = (qc, UnivConstraints.add u lc)

let of_qualities qc = make qc UnivConstraints.empty

let of_univs lc = make ElimConstraints.empty lc

let set_qualities qc (_,lc) = make qc lc

let set_univs lc (qc,_) = make qc lc

let empty = (ElimConstraints.empty, UnivConstraints.empty)

let is_empty (qc, lc) =
  ElimConstraints.is_empty qc && UnivConstraints.is_empty lc

let equal (qc, lc) (qc', lc') =
  ElimConstraints.equal qc qc' && UnivConstraints.equal lc lc'

let union (qc, lc) (qc', lc') =
  (ElimConstraints.union qc qc', UnivConstraints.union lc lc')

let fold (qf, lf) (qc, lc) (x, y) =
  (ElimConstraints.fold qf qc x, UnivConstraints.fold lf lc y)

let diff (qc, lc) (qc', lc') =
  (ElimConstraints.diff qc qc', UnivConstraints.diff lc lc')

let elements (qc, lc) =
  (ElimConstraints.elements qc, UnivConstraints.elements lc)

let filter_qualities f (qc, lc) =
  make (ElimConstraints.filter f qc) lc

let filter_univs f (qc, lc) =
  make qc @@ UnivConstraints.filter f lc

let pr prv prl (qc, lc) =
  let open Pp in
  let ppelim = if ElimConstraints.is_empty qc then mt()
               else ElimConstraints.pr prv qc ++ str"," in
  v 0 (ppelim ++ UnivConstraints.pr prl lc)

module HPConstraints =
  Hashcons.Make(
    struct
      type t = pconstraints
      let hashcons (qf, uf) =
        let hqf, qf = ElimConstraints.hcons qf in
        let huf, uf = UnivConstraints.hcons uf in
        Hashset.Combine.(combine hqf huf), (qf, uf)
      let eq (qc, uc) (qc', uc') =
        qc == qc' && uc == uc'
    end)

let hcons =
  Hashcons.simple_hcons
    HPConstraints.generate
    HPConstraints.hcons ()

(** A value with universe constraints. *)
type 'a constrained = 'a * t

let constraints_of (_, cst) = cst

(** Constraints functions. *)

type 'a constraint_function = 'a -> 'a -> t -> t

let enforce_eq_univ u v c =
  (* We discard trivial constraints like u=u *)
  if Level.equal u v then c
  else add_univ (u, UnivConstraint.Eq, v) c

let enforce_leq_univ u v c =
  if Level.equal u v then c
  else add_univ (u, UnivConstraint.Le, v) c

let enforce_eq_quality q1 q2 csts =
  if Quality.equal q1 q2 then csts
  else add_quality (q1, ElimConstraint.Equal, q2) csts

let enforce_elim_to q1 q2 csts =
  if QGraph.ElimTable.eliminates_to q1 q2 then csts
  else add_quality (q1, ElimConstraint.ElimTo, q2) csts

module ContextSet = struct
  type t = Level.Set.t constrained

  let of_lvl_set s : t = (s, empty)
  let singleton_lvl l = of_lvl_set (Level.Set.singleton l)

  let empty = (Level.Set.empty, empty)
  let is_empty (univs, cst) = Level.Set.is_empty univs && is_empty cst

  let equal (univs, cst as x) (univs', cst' as y) =
    x == y || (Level.Set.equal univs univs' && equal cst cst')

  let union (univs, cst as x) (univs', cst' as y) =
    if x == y then x
    else Level.Set.union univs univs', union cst cst'

  let append (univs, cst) (univs', cst') =
    let univs = Level.Set.fold Level.Set.add univs univs' in
    let cst = fold (ElimConstraints.add, UnivConstraints.add) cst cst' in
    (univs, cst)

  let diff (univs, cst) (univs', cst') =
    Level.Set.diff univs univs', diff cst cst'

  let add_level u (univs, cst) =
    Level.Set.add u univs, cst

  let add_constraints cst' (univs, cst) =
    union (univs, cst) (Level.Set.empty, cst')

  let add_univ_constraints cst' (univs, cst) =
    union (univs, cst) (Level.Set.empty, of_univs cst')

  let add_elim_constraints cst' (univs, cst) =
    union (univs, cst) (Level.Set.empty, of_qualities cst')

  let filter_out_constant_qualities (univs, csts) =
    let csts = filter_qualities
                 (fun (q1,_,q2) -> not (Quality.is_qconst q1 && Quality.is_qconst q2))
                 csts in
        (univs, csts)

  let pr prv prl (univs, cst as ctx) =
    let open Pp in
    if is_empty ctx then mt() else
      hov 0 (h (Level.Set.pr prl univs ++ str " |=") ++ brk(1,2) ++ h (pr prv prl cst))

  let constraints (_univs, cst) = cst
  let elim_constraints (_, (csts,_)) = csts
  let univ_constraints (_, (_,csts)) = csts
  let levels (univs, _cst) = univs

  let size (univs,_) = Level.Set.cardinal univs

  module HContextSet =
  Hashcons.Make(
    struct
      type nonrec t = t
      let hashcons (lvls, csts) =
        let hlvls, lvls = Univ.Level.Set.hcons lvls in
        let hcsts, csts = hcons csts in
        Hashset.Combine.combine hlvls hcsts, (lvls, csts)
      let eq (qc, uc) (qc', uc') =
        qc == qc' && uc == uc'
    end)

  let hcons = Hashcons.simple_hcons HContextSet.generate HContextSet.hcons ()
end

type 'a in_poly_context_set = 'a * ContextSet.t
