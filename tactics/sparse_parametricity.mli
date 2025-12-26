open Names
open Declarations
open EConstr
open Evd
open Environ
open Entries
open LibBinding
open State

  (** {6 Lookup Sparse Parametricity } *)

(** Given an inductive [ind] nested with [ind_nested], look up the sparse
    parametricity and the local fundamental theorem of [ind_nested].
    Raise a warning one of them is not found. *)
val lookup_sparse_parametricity : inductive -> inductive -> (GlobRef.t * GlobRef.t) option

  (** {6 Instantiate Sparse Parametricity } *)

(** Given the instantiation of uniform parameters [constr array] with their
    strictly positivity [bool list], it returns the instantiation of the uniform parameters
    of the sparse parametricity using the predicates [constr option array] and
    [fun ... => True] if the given value is [None]. *)
val instantiate_sparse_parametricity :
  constr array -> bool list -> constr option array -> constr array State.t

(** Given the instantiation of uniform parameters [constr array] with their
    strictly positivity [bool list], it returns the instantiation of the uniform parameters
    of the local fundamental theorem using the predicates [constr option array] and their proofs [constr option array],
    and [fun ... => True] and [fun ... => I] if the given values are [None]. *)
val instantiate_fundamental_theorem  :
  constr array -> bool list -> constr option array -> constr option array -> constr array State.t

  (** {6 View for Arguments } *)

type head_arg =
  | ArgIsSPUparam of int * constr array
  (** constant context, position of the uniform parameter, args *)
  | ArgIsInd of int * constr array * constr array
  (** constant context, position of the one_inductive body, inst_nuparams inst_indices *)
  | ArgIsNested of MutInd.t * int * mutual_inductive_body * bool list
                    * one_inductive_body * constr array * constr array
  (** constant context, ind_nested, mutual and one body, strictly positivity of its uniform parameters,
      instantiation uniform paramerters, and of both non_uniform parameters and indices *)
  | ArgIsCst

(** View to decompose arguments as [forall locs, X] where [X] is further decomposed
    as a uniform parameter, the inductive, a nested argument or a constant. *)
type arg = rel_context * head_arg

val view_arg : MutInd.t -> mutual_inductive_body -> access_key list -> bool list -> constr -> arg State.t

(** {6 WIP } *)

val gen_sparse_parametricity : env -> evar_map -> MutInd.t -> einstance ->
    mutual_inductive_body -> evar_map * mutual_inductive_entry

val gen_fundamental_theorem : env -> evar_map -> MutInd.t -> MutInd.t -> int -> einstance ->
  mutual_inductive_body -> evar_map * constr
