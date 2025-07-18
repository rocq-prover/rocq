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

(** Locus : positions in hypotheses and goals. *)

(** ['a or_var] represents either a value of type ['a] or a variable. *)
type 'a or_var =
  | ArgArg of 'a
  | ArgVar of lident

(** {6 Occurrences} *)

(** Occurences in a hypothesis or conclusion. *)
type 'a occurrences_gen =
  | AllOccurrences
  | AtLeastOneOccurrence
  | AllOccurrencesBut of 'a list (** The list should be non-empty. *)
  | NoOccurrences
  | OnlyOccurrences of 'a list (** The list should be non-empty. *)

type occurrences_expr = (int or_var) occurrences_gen
type 'a with_occurrences_expr = occurrences_expr * 'a

type occurrences = int occurrences_gen
type 'a with_occurrences = occurrences * 'a


(** {6 Locations} *)

(** In a hypothesis, occurrences can refer to the body (if any), to the type, or to both. *)
type hyp_location_flag = InHyp | InHypTypeOnly | InHypValueOnly

(** {6 Abstract clauses expressions} *)

type 'a hyp_location_expr = 'a with_occurrences_expr * hyp_location_flag

(** A [clause_expr] (and its instance [clause]) denotes occurrences and
   hypotheses in a goal in an abstract way; in particular, it can refer
   to the set of all hypotheses independently of the effective contents
   of the current goal.

   Concerning the field [onhyps]:
   - [None] means *on every hypothesis*.
   - [Some hyps] means on hypotheses belonging to [hyps]. *)
type 'id clause_expr =
  { onhyps : 'id hyp_location_expr list option;
    concl_occs : occurrences_expr }

type clause = Id.t clause_expr

(** {6 Concrete view of occurrence clauses} *)

(** [clause_atom] refers either to:
    - Some occurrences in a hypothesis.
    - Some occurrences in the conclusion .*)
type clause_atom =
  | OnHyp of Id.t * occurrences_expr * hyp_location_flag
  | OnConcl of occurrences_expr

(** A [concrete_clause] is a collection of occurrences in hypotheses
    and in the conclusion. *)
type concrete_clause = clause_atom list


(** {6 A weaker form of clause with no mention of occurrences} *)

(** A [hyp_location] is a hypothesis together with a location in this
    hypothesis (body, type, or both). *)
type hyp_location = Id.t * hyp_location_flag

(** A [goal_location] is either:
    - A hypothesis (together with a location in this hypothesis).
    - The conclusion (represented by [None]). *)
type goal_location = hyp_location option


(** {6 Simple clauses, without occurrences nor location} *)

(** A [simple_clause] is a set of hypotheses, possibly extended with
   the conclusion (conclusion is represented by None). *)
type simple_clause = Id.t option list

(** {6 Occurences modulo conversion} *)

(** A notion of occurrences allowing to express "all occurrences
    convertible to the first which matches". *)
type 'a or_like_first = AtOccs of 'a | LikeFirst
