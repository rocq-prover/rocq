(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** A model of universe constraints *)

open Univ

(** {1 Universe model and declarations} *)

type locality =
  | Global
  | Local
(** A graph can be local or global: this information is inherited by all universe and constraint additions.
    One can turn a global graph into a local one only once, and never go back, see [set_local]. *)

type t
(** The type of models *)

val empty : t
(** The empty, global model, keeping clauses irredundant and prime (unless
  [keep_redundant_premises] is applied) *)

exception AlreadyDeclared
val add : ?rigid:bool -> Level.t -> t -> t
(** All points must be pre-declared through this function before
    they can be mentioned in the others. NB: use [rigid] to
    prefer to keep the node canonical if it is made equal to another *)

exception Undeclared of Level.t
(** This exception is raised by the functions below taking a Level.t/Universe.t input
  that contains an undeclared level, i.e. one that was never added, or was removed. *)

val is_declared : t -> Level.t -> bool
(** Check if a level was previously declared in the graph *)

val check_declared : t -> Level.Set.t -> (unit, Univ.Level.Set.t) result
(** Check if a set of levels are declared and return the undeclared ones on error. *)

val domain : t -> Level.Set.t
(** Return the set of registered universe variables *)

(** {1 Checking constraints} *)

type 'a check_function = t -> 'a -> 'a -> bool

val check_eq : Universe.t check_function
val check_leq : Universe.t check_function

val with_check_cache : (unit -> 'a) -> 'a
(** [with_check_cache f] runs [f ()] keeping the answers of the checks in the models they are
  asked of, e.g. during the typechecking of the kernel, where the same checks are asked many times
  of the graph of the environment. The positive answers are kept by the models with more clauses
  (e.g. built by [enforce_constraints]), the negative ones by the models with fewer clauses (e.g.
  built by [Internal.remove]). They are not kept by default. *)

(** {1 Enforcing constraints} *)

type level_equivalences = (Level.t * (Level.t * int)) list
(** The equalities created by enforcing constraints or setting a universe, in the order they were
  found: [(u, (v, k))] means that [u] is now an alias of [v + k], with [k >= 0], [v] being
  canonical when the pair is produced. A later pair may make [v] an alias in turn: [normalize]
  gives the current representative. *)

val enforce_eq : Universe.t -> Universe.t -> t -> (t * level_equivalences) option
val enforce_leq : Universe.t -> Universe.t -> t -> (t * level_equivalences) option
val enforce_lt : Universe.t -> Universe.t -> t -> (t * level_equivalences) option
val enforce_constraint : UnivConstraint.t -> t -> (t * level_equivalences) option

val enforce_constraints : UnivConstraint.t list -> t -> (t * level_equivalences) option
(** Enforces the constraints all at once: their clauses are added to the model, then a model is
  inferred, and only then are the equalities they create merged. This is more efficient than
  enforcing them one at a time. *)

val localize : UnivConstraint.t list -> t -> t
(** [localize csts m] makes the clauses of [csts] that are global clauses of [m] local, e.g. the
  constraints of side effects that are inlined instead of declared. *)

val keep_redundant_premises : t -> t
(** The clauses with several premises are kept as enforced, instead of removing the ones that the
  other clauses entail and dropping the premises that they make redundant: then the clauses of the
  graph are the ones of the enforced constraints, which [remove_if_entailed] needs, as a removed
  or simplified clause depends on other ones. *)

val remove_if_entailed : UnivConstraint.t -> t -> t option
(** [remove_if_entailed c m]: when the clauses of the constraint [c] are local clauses of [m] (see
  [set_local]) that the other clauses entail, [m] without them. As only entailed clauses are
  removed, the result has the same models.
  NB: the clauses of [m] are the ones of the enforced constraints only when no clause was removed
  nor premise dropped (see [keep_redundant_premises]) and the universes made equal are the ones of
  the enforced equalities. Otherwise, the clauses of [c] may be entailed by the other clauses of
  [m] but not by the other enforced constraints: e.g. [u <= max(v, w)] becomes [u <= w] because of
  [v <= w], which it then entails along with [u <= v]. *)

(** {1 Explanations of inconsistencies} *)

type extended_constraint_type =
  | ULe | ULt | UEq

type explanation =
  | Chain of Universe.t * (extended_constraint_type * Universe.t) list
  (** [Chain (u0, [(r1, u1); ...; (rn, un)])] is [u0 r1 u1 ... rn un] *)
  | Constraints of (Universe.t * extended_constraint_type * Universe.t) list
  (** Constraints of the graph which are together inconsistent with the enforced one *)

val get_explanation : UnivConstraint.t -> t -> explanation
(** Assuming that the corresponding call to [enforce_*] returned [None], this
    will give a trace for the failure: a chain of inequalities refuting the constraint
    when there is one, otherwise a minimal set of constraints inconsistent with it. *)

(** {1 Canonical representatives and substitution} *)

val normalize : t -> Level.t -> Universe.t option
(** Normalize a level to its canonical representative.
  This uses the internally maintained substitution from levels to universes.
  @return A canonical universe: each level in the universe is canonical w.r.t. the given model.
  [None] for a canonical level, and also for a level the model does not declare, e.g. a bound
  universe variable: as a substitution on terms, [normalize] leaves the levels it does not know. *)

exception InconsistentEquality
exception OccurCheck
exception NotCanonical

val set : ?entailed:bool -> Level.t -> Universe.t -> t -> t * level_equivalences
(** [set idx u model] substitutes universe [u] for all occurrences of [idx] in model, resulting
  in a set of constraints that no longer mentions [idx]. This is stronger than [enforce_eq idx u],
  as the [idx] universe is dropped from the constraints altogether. Returns a list of universes
  that are also made equal by the new constraint and are also substituted by [u] in the resulting graph.
  With [~entailed:true], the clauses of the level, once substituted, are known to be entailed:
  the search for the equalities they create is skipped.
  @raise InconsistentEquality if setting [l = u] results in an unsatisfiable constraint
  @raise OccurCheck if the universe contains the level, up to equivalence in the graph
  @raise NotCanonical if the given level to set is not canonical *)

val clause_count : t -> Level.t -> int
(** [clause_count m l] is the number of clauses of the canonical node of [l]
  (0 if [l] is an alias): an estimate of the cost of
  [set l _ m], which moves all of them. *)

(** {1 Minimization and bounds} *)

type 'a simplification_result =
  | HasSubst of 'a * level_equivalences * Universe.t
  (** [HasSubst (m, equivs, b)]: the level given to [minimize] or [maximize] is set to its bound
    [b] in [m] (see [set]), [equivs] being the other equalities this created *)
  | NoBound
  (** The level has no such bound *)
  | CannotSimplify
  (** The level has a bound it cannot be set to: one which is not a universe (e.g. [l >= u - 1] from
    [u + 1 <= l + 2]), several upper bounds for [maximize], a bound inconsistent with the other
    constraints, or, with [~require_entailed:true], one that would constrain the other universes.
    Also when the level is an alias. *)

val minimize : ?require_entailed:bool -> Level.t -> t -> t simplification_result
(** [minimize l m] sets [l] to its greatest lower bound, the maximum of the universes [u + k]
  with a clause [u + k <= l] of [m] where [l] is the only premise, when every [k] is
  non-negative.
  With [~require_entailed:true], only when the clauses where the level is one of several
  premises still hold, entailed by the others, once it is set to its lower bound: otherwise the
  substitution would constrain the other universes of these clauses *)

val maximize : Level.t -> t -> t simplification_result
(** [maximize l m] sets [l] to its upper bound when a single clause [l + k <= max(e_i + k_i)] of
  [m] bounds it from above, with [k <= k_i] for every [i]: [l] becomes [max(e_i + (k_i - k))]. *)

val has_upper_bound : Level.t -> t -> bool
(** [has_upper_bound l m] holds when a clause of [m] concludes on [l], i.e. bounds it from above
  (also when [l] is an alias) *)

val lower_bound : Level.t -> t -> Universe.t option
(** [lower_bound l m] is the greatest lower bound of [l] in [m] given by the clauses where [l] is
  the only premise, if any *)

val substitution_entailed : (Level.t * Level.t) list -> t -> bool
(** [substitution_entailed subst m] holds when [m] entails every clause of the levels [u] of
  [subst], once each is substituted by its [v]. Then the constraints on the other universes are
  the same after the substitution: the models of [m] restricted to them are models of the
  substituted clauses, and a model of these extends to one of [m], with each [u] set to its [v]. *)

val substitution_entailed_univ : ?free:(Level.t -> bool) -> (Level.t * Universe.t) list -> t -> bool
(** [substitution_entailed_univ] is [substitution_entailed] for substitutions by universes, e.g.
  [max(v, w)]. With [free], the universes which may take any value, a substituted clause also holds
  when it can be satisfied by raising its [free] premise, if it has only one (whose upper bounds
  are single universes which can be raised too), or by lowering its [free] conclusion to its lower
  bounds: it then constrains no other universe. *)

val substitution_failures_univ : ?free:(Level.t -> bool) -> (Level.t * Universe.t) list -> t -> Level.t list option
(** [substitution_failures_univ subst m] is the list of the levels [u] of [subst] whose clauses do
  not hold once substituted (see [substitution_entailed_univ]), [None] when one of them is an
  alias or is not declared *)

(** {1 Constraints of a graph} *)

type 'a constraint_fold = UnivConstraint.t -> 'a -> 'a

val constraints_of : t -> ?only_local:bool -> 'a constraint_fold -> 'a ->
  Level.Set.t * 'a * (locality * Universe.t) Level.Map.t
(** [constraints_of graph ?only_local fold acc = (levels, acc', equivs)]

  Computes the constraints modeled by the graph.
  If [only_local] is [true] (default is [false]), [levels] is the set of universes that were declared locally
  (since the last and only possible [set_local] call on the graph).
  The [Le] constraints are passed to a folding function starting with [acc] whose result is returned as [acc'].
  Finally [equivs] contains a level substitution corresponding to [Eq] constraints. *)

val constraints_for : kept:Level.Set.t -> t -> 'a constraint_fold -> 'a -> 'a
(** [constraints_for ~kept m fold acc] folds [fold] over the constraints between the [kept]
  universes derivable in [m]. *)

val variables : local:bool -> with_subst:bool -> t -> Level.Set.t
(** Computes the set of registered variables, optionally restricted to local ones, and
  optionally including the substituted variables. *)

val subst : local:bool -> t -> (locality * Universe.t) Level.Map.t
(** Substitution from (local) levels to universes.
   N.B.: slightly expensive to compute, better use [normalize]. *)

(** {1 Local / global and flexible / rigid universes}

  A graph extending a global one (see [set_local]) distinguishes the universes, clauses and
  equations added since, which are local, from the global ones. A universe is also rigid or
  flexible (see [add]): only the non-rigid aliases are substituted in terms. *)

val set_local : t -> t
(** [set_local m] is [m] as the global graph of a local one: the universes, clauses and
  equations added from then on are local. *)

val set_locality : locality -> Level.t -> t -> t
(** [set_locality local l m] makes the universe [l], canonical or substituted, local or
  global. The equation of a substituted universe made local is local too. *)

val enforce_global_constraints : UnivConstraint.t list -> t -> (t * level_equivalences) option
(** As [enforce_constraints], but the constraints are global even in a local graph (see
  [set_local]): they supersede the same local ones. *)

val switch_locality : Level.t -> t -> t
(** Flips the locality of a canonical universe. *)

val is_local : t -> Level.t -> bool
(** Whether a universe, canonical or substituted, is local. *)

type local_status = NotLocal | LocalNode | LocalAlias

val local_status : t -> Level.t -> local_status
(** [local_status m l] tells if [l] is a local canonical universe, or an alias whose
  equation is local, as considered by [constraints_of ~only_local:true]. *)

val normalize_flexible : t -> Level.t -> Universe.t option
(** As [normalize], but only for the non-rigid levels (see [add]): a rigid level stays as it
  is, even when it is equal to another universe. As [normalize], [None] for an undeclared level. *)

val alias_rigidity : t -> Level.t -> bool option
(** [alias_rigidity m l] is [Some rigid] when [l] is substituted, [rigid] telling whether [l]
  was rigid, and [None] when [l] is canonical. *)

val is_flexible : t -> Level.t -> bool
(** The flexible universes are the local canonical universes which are not rigid (see [add]):
  the unification variables of the elaborator. A substituted universe is not flexible, nor an
  undeclared one: [is_flexible] is [false] for it, as its callers may ask it of the levels of terms
  coming from other evar maps. *)

val flexible_local_levels : t -> Level.Set.t
(** The flexible universes of the graph (see [is_flexible]) *)

val set_rigid : bool -> Level.t -> t -> t
(** [set_rigid rigid l m] makes the universe [l] rigid or flexible. For a substituted universe,
  this tells whether it is substituted in terms (see [normalize_flexible]). *)

val is_context_level : t -> Level.t -> bool
(** The universes of the context of the elaborator: the local canonical universes and the local
  rigid substituted ones, which stay in the terms. The local non-rigid substituted universes are
  substituted in terms, so they are not part of it. *)

val local_levels : t -> Level.Set.t
(** The universes of the context of the elaborator (see [is_context_level]) *)

val rigid_local_levels : t -> Level.Set.t
(** The rigid universes of the context: [local_levels] but the flexible universes (see
  [is_flexible]) *)

(** {1 Representation} *)

type node =
| Alias of Universe.t
| Node of (int * Universe.t) list (** Nodes [(k_i, u_i); ...] s.t. u + k_i <= u_i *)

type model_repr = node Level.Map.t

val model_repr : local:bool -> t -> model_repr
(** Get a representation of the model, optionally selecting only local universes and constraints. *)

val pr_model : ?local:bool -> t -> Pp.t
(** Print the model. Optionally print only the local universes and constraints. *)

val valuation : t -> int Level.Map.t
(** [valuation m] is a valuation of the universes of [m] in the natural numbers which satisfies its
  constraints: every universe, canonical or alias, gets a value [>= 0], [Set] gets [0], and an alias
  gets the value of its expression. *)

(** {1 Internal functions, used by [UGraph]} *)

module Internal :
sig
  val statistics : t -> Pp.t
  (** Print statistics on the model, its clauses and values *)

  val check_invariants : required_canonical:(Level.t -> bool) -> t -> unit
  (** [check_invariants ~required_canonical m] checks the invariants of the representation of [m],
    raising an error which describes the first one that is broken: the clauses only mention
    canonical universes, are simplified (sorted premises, neither trivial nor contradictory, no
    shift common to the conclusion and the premises, no premise [Set + k] below another one), have
    non-negative increments, and are stored both as backward clauses of their conclusion and as
    forward clauses of their premises; the local universes and equations are recorded as such;
    the aliases are expressions [v + k] with [k >= 0] on canonical universes, and no universe
    satisfying [required_canonical] is an alias (e.g. [Set] for [UGraph]). It is costly: for
    debugging. *)

  val remove : Level.Set.t -> t -> t
  (** [remove l m] removes the [l] universes from [m], keeping the constraints between the
    other universes that they entail, see [UGraph.remove].
    This is not very efficient, so avoid using it if possible.
  *)

  val remove_set_clauses : Level.t -> t -> t
  (** Hack for template-polymorphism. [remove_set_clauses u m] removes all [u -> Set+0] clauses from the model *)
end
