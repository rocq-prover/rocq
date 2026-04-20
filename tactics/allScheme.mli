open Names
open Declarations
open EConstr
open Evd
open Environ
open Entries
open LibBinding
open State

  (** {6 Strictly Positive Uniform Parameters } *)

(** Computes which uniform parameters are strictly positive in a mutual inductive body *)
val compute_params_rec_strpos : env -> MutInd.t -> mutual_inductive_body -> bool list

  (** {6 Lookup All Predicate and its Theorem } *)

(** Compute the default positivity of the uniform parameters, and generates the
    suffix for naming the all predicate, and its predicate, as well as the key
    for registering.
    If a positivity specification is given by users [bool list option], it is
    checked to be included in the default one, and the suffix are modified accordingly. *)
val compute_positive_uparams_and_suffix : env -> MutInd.t -> mutual_inductive_body ->
  Id.t list option -> bool list * (string * string) * (string * string)

(** Lookup the partial [all] predicate and its theorem for [ind_nested] for [args_are_nested].
    If they are not found, lookup the general [all] predicate and its theorem.
    Returns if the partial [all] was found, and the global references.
    Raise a warning if none is found. *)
val lookup_all_theorem : inductive -> GlobRef.t -> bool list -> (bool * GlobRef.t * GlobRef.t) option

  (** {6 Instantiate the All Predicate and its Theorem } *)

(** Make the [all] predicate for a fresh instance and using [Typing.checked_appvect], given:
    - whether the [all] predicate is the partial one, or the general one [partial_nesting:bool]
    - the positivity of each uniform parameter [bool list]
    - the instantiation of the uniform parameter of the inductive type [constr array]
    - the instation of the fresh predicate [constr option array], using [fun ... => True]
      if the values are none, and [all] is the general predicate
    - the instantiation of the non-uniform parameters and indices
    - the argument to apply it to
*)
val make_all_predicate : partial_nesting:bool -> GlobRef.t -> bool list -> constr array ->
  constr option array -> constr array -> constr -> constr State.t

(** Make the theorem for the [all] predicate for a fresh instance and using [Typing.checked_appvect], given:
    - whether the [all] predicate is the partial one, or the general one [partial_nesting:bool]
    - the positivity of each uniform parameter [bool list]
    - the instantiation of the uniform parameter of the inductive type [constr array]
    - the instation of the fresh predicate and the proofs they hold [constr option array],
      using [fun ... => True] and [fun _ => I] if the values are none, and [all] is the general predicate
    - the instantiation of the non-uniform parameters and indices
    - the argument to apply it to
*)
val make_all_theorem : partial_nesting:bool -> GlobRef.t ->  bool list -> constr array -> constr option array ->
  constr option array -> constr array -> constr -> constr State.t

  (** {6 View for Arguments } *)

type head_argument =
  | ArgIsSPUparam of int * constr array
  (** position of the uniform parameter, args *)
  | ArgIsInd of int * constr array * constr array
  (** position of the one_inductive body, inst_nuparams, inst_indices *)
  | ArgIsNested of GlobRef.t * bool list
                    * rel_context * constr array * constr array
  (** nested_container, strict positivity of its uniform parameters,
      uniform parameters, their instantiation, and instantiation of both non_uniform parameters and indices *)
  | ArgIsCst

(** View to decompose arguments as [forall locs, X] where [X] is further decomposed
    as a uniform parameter, the inductive, a nested argument or a constant. *)
type argument = rel_context * head_argument

(** Decompose the argument in [it_Prod_or_LetIn local, X] where [X] is a uniform parameter, Ind, nested or a constant *)
val view_argument : MutInd.t -> mutual_inductive_body -> access_key list ->
  bool list -> constr -> argument State.t

  (** {6 Generate All Predicate } *)

val generate_all_predicate : env -> evar_map -> MutInd.t -> einstance ->
  mutual_inductive_body -> bool list -> string -> UState.t * mutual_inductive_entry

(** {6 Generate the Theorem for the All Predicate } *)

val generate_all_theorem : env -> evar_map -> MutInd.t -> MutInd.t -> int -> einstance ->
  mutual_inductive_body -> bool list -> evar_map * constr
