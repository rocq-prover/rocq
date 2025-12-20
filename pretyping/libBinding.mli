(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)


(** This file contain a lightweight API for meta-programming: to traverse
    binders and either keep them, create new ones.

    With this API, variables are refered abstractly using [access_key].
    For instance, to compute the term associated to a variable (debruijn variable)
    one should use [get_term : acces_key -> constr t].
    Such terms can easily be created using the monadic bind: [let* t = get_term k in ...].

    So that the users do not have to create [access_key] themselves, and make mistakes,
    the creation of [access_key] is directly handled by the functions creating binders.
    For instance, to create a product [Prod A B], the body [B] has type
    [access_key -> constr t] where the [access_key] of the variable [A].
    To easily write code, it recomended to use the notation [let@]:
    [let@ key_A = make_binder naming na A in (* def of B : constr t *) ].

    It also provides facilities for naming variables, the different functions
    taking [type naming_scheme = rel_declaration -> rel_declaration t] as arguments.
    A few basic ones are provided.

    To do so, the API uses a reader monad with a state that contains:
    - the environment (Declarations + local context),
    - the evar_map,
    - the set of names already used,
    - a substitution from the former context of the term being traversed,
      to the context of the term being created which may differ due to
      addition of new binders
*)


open Evd
open EConstr
open Names
open Declarations
open Environ

module State :
  sig
    type state

    (* Monads *)
    type 'a t = state -> evar_map * 'a
    val return : 'a -> 'a t
    val bind : 'a t -> ('a -> 'b t) -> 'b t
    val map : ('a -> 'b) -> 'a t -> 'b t
    val run : env -> evar_map -> 'a t -> evar_map * 'a

    (* Access the current state *)
    val get_env     : env t
    val get_sigma   : evar_map t
    val get_names   : Nameops.Fresh.t t
    val get_state   : state t
    val get_context : rel_context t
    val update_sigma : state -> evar_map -> state

  (** {6 Weaken Functions From the Former Context to the New Context } *)

    (** Weaken a term defined in the former context by applying [state.subst]. *)
    val weaken : constr -> constr t

    (** Weaken a declaration defined in the former context by applying [state.subst]. *)
    val weaken_rel : rel_declaration -> rel_declaration t

    (** Weaken a context defined in the former context by applying [state.subst]. *)
    val weaken_context : rel_context -> rel_context t

  (** {6 Access Key } *)

  (** Type of access keys for the State API *)
  type access_key
  val make_key : int -> access_key t

  (** {6 Push Functions } *)

    (** Add a former definition [decl] to a state [s].
        It returns the new state, and an access key to acces the declaration.
        It supposes [decl] is well-typed in the current context. *)
    val push_old_rel : rel_declaration -> (state * access_key) t

    (** Add a new definition [decl] to a state [s].
        It returns the new state, and an access key to acces the declaration.
        It supposes [decl] is well-typed in the current context. *)
    val push_fresh_rel : rel_declaration -> (state * access_key) t

  (** {6 Access Functions } *)

    (** {7 Access Terms } *)

    (** Compute the debruijn variable associated
        to an [access_key] in the context [s : state]. *)
    val get_term : access_key -> constr t

    (** Compute the debruijn variable associated
        to the [i]-th [access_key] in the context [s : state]. *)
    val geti_term : access_key list -> int -> constr t

    (** Compute the debruijn variable associated
        to the [i]-th, [j]-th [access_key] in the context [s : state]. *)
    val getij_term : access_key list list -> int -> int -> constr t

    (** Compute the debruijn variables associated
        to a list of [access_key] in the context [s : state]. *)
    val get_terms : access_key list -> (constr array) t

    (** {7 Access Types } *)

    (** Compute the type of the variable associated
        to an [access_key] in the context [s : state]. *)
    val get_type : access_key -> types t

    (** Compute the type of the variable associated
        to the [i]-th [access_key] in the context [s : state]. *)
    val geti_type : access_key list -> int -> types t

    (** Compute the type of the variable associated
        to the [i]-th, [j]-th [access_key] in the context [s : state]. *)
    val getij_type : access_key list list -> int -> int -> types t

    (** Compute the type of the variable associated
        to a list of [access_key] in the context [s : state]. *)
    val get_types : access_key list -> (types array) t

    (** {7 Access Binder Annotations } *)

    (** Compute the [binder_annot] of the variable associated
        to an [access_key] in the context [s : state]. *)
    val get_aname : access_key -> Name.t binder_annot t

    (** Compute the [binder_annot] of the variable associated
        to the [i]-th [access_key] in the context [s : state]. *)
    val geti_aname : access_key list -> int -> (Name.t binder_annot) t

    (** Compute the [binder_annot] of the variable associated
        to the [i]-th, [j]-th [access_key] in the context [s : state]. *)
    val getij_aname : access_key list list -> int -> int -> (Name.t binder_annot) t

    (** Compute the [binder_annot] of the variable associated to a list of
        [access_key] in the context [s : state]. *)
    val get_anames : access_key list -> (Name.t binder_annot array) t

  (** {6 Debug Functions } *)
  val list_mapi : (int -> 'a -> 'b t) -> 'a list -> 'b list t
  val array_mapi : (int -> 'a -> 'b t) -> 'a array -> 'b array t
  val array_map2i : (int -> 'a -> 'b -> 'c t) -> 'a array -> 'b array -> 'c array t

  (** {6 Debug Functions } *)

    (** Print function for debugging. *)
    (* val print_state : (env -> evar_map -> constr -> Pp.t) -> Pp.t t *)

    (** Print function for debugging. *)
    (* val print_substitution : (env -> evar_map -> constr -> Pp.t) -> Pp.t t *)
  end

open State

(** {6 Fold Functions for State } *)

(** This function is meant to iterate a function creating binders.
    ['c -> 'b list -> 'b list] explains which [access_key] to save, e.g. [::] to save them all. *)
val fold_right_state : ('c -> 'b list -> 'b list) -> 'a list ->
  (int -> 'a -> ('c -> 'd t) -> 'd t) -> ('b list -> 'd t) -> 'd t

(** This function is meant to iterate a function creating binders: [int -> 'a -> ('c -> 'd t) -> 'd t].
['c -> 'b list -> 'b list] explains which [access_key] to save, e.g. [::] to save them all. *)
val fold_left_state  : ('c -> 'b list -> 'b list) -> 'a list ->
  (int -> 'a -> ('c -> 'd t) -> 'd t) -> ('b list -> 'd t) -> 'd t

(** This function is meant to iterate a function creating binders.
    ['c -> 'b list -> 'b list] explains which [access_key] to save, e.g. [::] to save them all. *)
val fold_right_state_3 : ('c -> 'b list -> 'b list) -> 'a list ->
(int -> 'a -> ('c * 'c * 'c -> 'd t) -> 'd t) -> ('b list * 'b list * 'b list -> 'd t) -> 'd t

(** This function is meant to iterate a function creating binders: [int -> 'a -> ('c -> 'd t) -> 'd t].
['c -> 'b list -> 'b list] explains which [access_key] to save, e.g. [::] to save them all. *)
val fold_left_state_3  : ('c -> 'b list -> 'b list) -> 'a list ->
(int -> 'a -> ('c * 'c * 'c -> 'd t) -> 'd t) -> ('b list * 'b list * 'b list -> 'd t) -> 'd t

(** {6 Naming Schemes for Binders } *)

type naming_scheme = rel_declaration -> rel_declaration t

(** Identity namming *)
val naming_id : naming_scheme

(** Name the binder using the head of the declaration's type if it [Anonymous]. *)
val naming_hd : naming_scheme

(** [naming_dep] if [true], [naming_id] otherwise  *)
val naming_hd_dep : bool -> naming_scheme

(** Uses the next fresh names available, using the head of the declaration's type if it [Anonymous]. *)
val naming_hd_fresh : naming_scheme

(** [naming_hd_fresh] if [true], [naming_id] otherwise  *)
val naming_hd_fresh_dep : bool -> naming_scheme

(** {6 Functions on Terms } *)


(** Reduce and decompose a term preserving letin *)
val ind_relevance : one_inductive_body -> einstance -> erelevance t

val whd_decompose_prod_decls : constr -> (rel_context * constr) t

val decompose_lambda_decls : constr -> (rel_context * constr) t

val decompose_app : constr -> (constr * constr array) t

val eta_expand_instantiation : constr array -> rel_context -> constr array t

val retyping_sort_of : constr -> esorts t

val typing_checked_appvect : constr -> constr array -> constr t

val fresh_global : GlobRef.t -> constr t

(** {6 Create a New Lambda, Product, or LetIn } *)

(** Status of the variable to bind *)
type freshness = Fresh | Old

(** Which binders to bind *)
type binder = Lambda | Prod

val fid : ('a -> 'b) -> 'a -> 'b
val fopt : ('a -> 'b) -> 'a option -> 'b option
val fropt : ('a -> 'b) -> ('c * 'a) option -> ('c * 'b) option

(** Add a declaration to the state given its [freshness] and a [naming_scheme],
    for a body defined in the updated state. *)
val add_decl : freshness -> naming_scheme -> rel_declaration ->
  (access_key -> 'a t) -> 'a t

(** Bind a declaration with [binder] or [LetIn], given its [freshness] and a [naming_scheme],
    for a body defined in the updated state. *)
val build_binder : ((constr -> constr) -> 'a -> 'b) -> binder -> freshness -> naming_scheme -> rel_declaration ->
  (access_key -> 'a t) -> 'b t

(** Create a new [binder] using a [naming_scheme], for a body in the updated state.
    When creating a fresh binder, the type of the variable needs to type check in the current context. *)
val make_binder : ((constr -> constr) -> 'a -> 'b) -> binder -> naming_scheme -> Name.t binder_annot -> types ->
  (access_key -> 'a t) -> 'b t

(** Keep a former [binder] using a [naming_scheme], for a body defined in the updated state. *)
val keep_binder : ((constr -> constr) -> 'a -> 'b) -> binder -> naming_scheme -> Name.t binder_annot -> types ->
  (access_key -> 'a t) -> 'b t

(** {6 Create Lambda, Product, or LetIn for Context} *)

(** Add a context to the state given its [freshness] and a [naming_scheme],
    for a body defined in the updated state [state * access_key list -> constr]. *)
val add_context : freshness -> naming_scheme -> rel_context ->
  (access_key list -> 'a t) -> 'a t

(** Add a context to the state given its [freshness] and a [naming_scheme],
    for a body defined in the updated state, where the [access_key] are split
    between [key_vars, key_letin, key_both]. *)
val add_context_sep : freshness -> naming_scheme -> rel_context ->
  (access_key list * access_key list * access_key list -> 'a t) -> 'a t

(** Bind a context with [binder] or [LetIn], given its [freshness] and a [naming_scheme],
    for a body defined in the updated state. *)
val closure_context : ((constr -> constr) -> 'a -> 'a) -> binder -> freshness ->
  naming_scheme -> rel_context -> (access_key list -> 'a t) -> 'a t

(** Bind a context with [binder] or [LetIn], given its [freshness] and a [naming_scheme],
    for a body defined in the updated state, where the [access_key] are split
    between [key_vars, key_letin, key_both]. *)
val closure_context_sep : ((constr -> constr) -> 'a -> 'a) -> binder -> freshness -> naming_scheme ->
  rel_context -> (access_key list * access_key list * access_key list -> 'a t) -> 'a t

(** Decompose a [constr] as [binder(s) local hd], then rebind it as
    [binder(s) local, binder hd, cc] *)
val rebind : ((constr -> constr) -> 'a -> 'a) -> binder -> freshness -> naming_scheme -> constr ->
  (access_key list * access_key -> 'a t) -> 'a t

(** [reads cxt binder cc_letin cc_var] go through a context [cxt],
    apply [binder] to each context declaration [decl] to it,
    then apply [cc_letin] if [decl] is a [LetIn], and [cc_var] otherwise.   *)
val read_by_decl :
  rel_context ->
  (rel_declaration -> (access_key -> constr t) -> constr t) ->
  (int -> access_key -> (access_key list -> constr t) -> constr t) ->
  (int -> access_key -> (access_key list -> constr t) -> constr t) ->
  (access_key list -> constr t) -> constr t

(** Iterate a binding function to each constructor or an inductive type. *)
val iterate_ctors : mutual_inductive_body -> one_inductive_body -> einstance ->
  (int -> rel_context * constr array -> ('a -> 'b t) -> 'b t) ->
  ('a list -> 'b t) -> 'b t

(** {6 Functions on Inductives} *)

(** Create a term refering to an inductive type given the [access_key]
    for uniform paramters, non-uniform parameters, and indices. *)
val make_ind : inductive * EInstance.t -> access_key list -> access_key list -> access_key list -> constr t

(** Create a term refering to the constructor of an inductive type given the [access_key]
    for uniform paramters, non-uniform parameters, and indices. *)
val make_cst : inductive * EInstance.t -> int -> access_key list -> access_key list -> constr array -> constr t

(** Create a term refering to an inductive type given the [access_key]
    for uniform paramters, non-uniform parameters, and indices. *)
val make_fix : 'a list -> int -> (int -> 'a -> int) ->
  (int -> 'a -> Name.t binder_annot) -> (int -> 'a -> types t) ->
  (access_key list * int * 'a -> constr t) -> constr t

(** Recover the indices of an inductive block, and weaken them in the current context. *)
val get_indices : one_inductive_body -> einstance -> rel_context t

(** Create a new match given:
  - A [naming_scheme] for the fresh indices, and arguments
  - The [mutual_inductive_body], [inductive], [one_inductive_body], [instance] on which the match is performed
  - The access keys for its uniform and non-uniform parameters
  - The parameters [constr array], and indices [constr array] of the term being matched
  - The return type of the match [access_key list -> access_key -> constr t]
  - The [relevance] of the match
  - The term being matched [constr]
  *)
val make_case_or_projections : naming_scheme -> mutual_inductive_body -> inductive -> one_inductive_body ->
  einstance -> access_key list -> access_key list -> constr array -> constr array ->
  (access_key list -> access_key -> types t) -> erelevance -> constr ->
  (access_key list * access_key list * access_key list * int -> constr t) -> constr t
