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
open Constr
open EConstr
open Environ
open Evd
open Unification
open Tactypes
open Locus

(** Main tactics defined in ML. This file is huge and should probably be split
    in more reasonable units at some point. Because of its size and age, the
    implementation features various styles and stages of the proof engine.
    This has to be uniformized someday. *)

(** {6 General functions. } *)

type evars_flag = bool     (* true = pose evars       false = fail on evars *)
type rec_flag = bool       (* true = recursive        false = not recursive *)
type advanced_flag = bool  (* true = advanced         false = basic *)
type clear_flag = bool option (* true = clear hyp, false = keep hyp, None = use default *)

(** Apply a tactic on a quantified hypothesis, an hypothesis in context
    or a term with bindings. *)

type 'a core_destruction_arg =
  | ElimOnConstr of 'a
  | ElimOnIdent of lident
  | ElimOnAnonHyp of int

type 'a destruction_arg =
  clear_flag * 'a core_destruction_arg

val onInductionArg :
  (clear_flag -> constr with_bindings -> unit Proofview.tactic) ->
    constr with_bindings destruction_arg -> unit Proofview.tactic

val force_destruction_arg : evars_flag -> env -> evar_map ->
    delayed_open_constr_with_bindings destruction_arg ->
    evar_map * constr with_bindings destruction_arg

val finish_evar_resolution : ?flags:Pretyping.inference_flags ->
  env -> evar_map -> (evar_map option * constr) -> evar_map * constr

(** {6 Pattern introduction tactics. } *)

(** [intro_patterns with_evars patt] introduces variables and processes them according
    to the introduction patterns [patt]. *)
val intro_patterns : evars_flag -> intro_patterns -> unit Proofview.tactic

(** Variant of [intro_patterns] which moves introduced variables to location [loc]. *)
val intro_patterns_to : evars_flag -> Id.t Logic.move_location -> intro_patterns ->
  unit Proofview.tactic

(** Variant of [intro_patterns_to] which introduces a single variable. *)
val intro_pattern_to : evars_flag -> Id.t Logic.move_location -> delayed_open_constr intro_pattern_expr ->
    unit Proofview.tactic

val intro_patterns_bound_to : evars_flag -> int -> Id.t Logic.move_location -> intro_patterns ->
  unit Proofview.tactic

(** [intros_patterns with_evars patt] implements the user-level "intros" tactic:
    - If [patt] is empty it will introduces as many variables as possible (using [intros]).
    - Otherwise it will behave as [intro_patterns with_evars patt]. *)
val intros_patterns : evars_flag -> intro_patterns -> unit Proofview.tactic

val specialize : constr with_bindings -> intro_pattern option -> unit Proofview.tactic

(** [unfold_body id] unfolds the definition of the local variable [id] in the conclusion
    and in all hypotheses. Fails if [id] does not have a body. *)
val unfold_body : Id.t -> unit Proofview.tactic

(** {6 Apply tactics. } *)

(** [apply t] applies the lemma [t] to the conclusion. *)
val apply : constr -> unit Proofview.tactic

(** Variant of [apply] which allows creating new evars. *)
val eapply : ?with_classes:bool -> constr -> unit Proofview.tactic

(** Variant of [apply] which takes a term with bindings (e.g. [apply foo with (x := 42)]). *)
val apply_with_bindings : constr with_bindings -> unit Proofview.tactic

(** Variant of [eapply] which takes a term with bindings (e.g. [eapply foo with (x := 42)]).
    - [with_classes] specifies whether to attempt to solve remaining evars using typeclass resolution. *)
val eapply_with_bindings : ?with_classes:bool -> constr with_bindings -> unit Proofview.tactic

(** [apply_with_bindings_gen ?with_classes advanced with_evars [(c1, t1); (c2, t2); ...]] is the most
    general version of [apply]. It applies lemmas [t1], [t2], ... in order.
    - [with_evars]: if [true] allow the creation of (non-goal) evars (i.e. setting [with_evars] to [true]
      gives the behaviour of [eapply]).
    - [with_classes]: if [true] attempt to solve remaining evars using typeclass resolution.
    - [advanced]: if [true] use delta reduction (constant unfolding) in unification,
      and descend under conjunctions in the conclusion.
    - [ci]: if [ti] is a hypothesis, [ci] tells whether to clear [ti] after applying it.
      If [ci] is [None] we use the default clear flag. *)
val apply_with_bindings_gen :
  ?with_classes:bool -> advanced_flag -> evars_flag -> (clear_flag * constr with_bindings CAst.t) list -> unit Proofview.tactic

(** Variant of [apply_with_bindings_gen] in which the terms are produced by tactics.  *)
val apply_with_delayed_bindings_gen :
  advanced_flag -> evars_flag -> (clear_flag * constr with_bindings Proofview.tactic CAst.t) list -> unit Proofview.tactic

(** Variant of [apply_with_bindings_gen] which works on a hypothesis instead of the goal. *)
val apply_in :
  advanced_flag -> evars_flag -> Id.t ->
    (clear_flag * constr with_bindings CAst.t) list ->
    intro_pattern option -> unit Proofview.tactic

(** Variant of [apply_in] in which the terms are produced by tactics.*)
val apply_delayed_in :
  advanced_flag -> evars_flag -> Id.t ->
    (clear_flag * constr with_bindings Proofview.tactic CAst.t) list ->
    intro_pattern option -> unit Proofview.tactic -> unit Proofview.tactic

val apply_type : typecheck:bool -> constr -> constr list -> unit Proofview.tactic

(** [cut_and_apply t] (where [t] has type [A -> B]) transforms a goal [ |- C ] into two goals
    [ |- B -> C ] and [ |- A ]. *)
val cut_and_apply : constr -> unit Proofview.tactic

(** {6 Elimination tactics. } *)

(** [simplest_elim t] eliminates [t] using the default eliminator associated to [t].
    It does not allow unresolved evars, and uses the default clear flag. *)
val simplest_elim : constr -> unit Proofview.tactic

(** [elim with_evars clear t eliminator] eliminates [t].
    - [with_evars]: if [true] we allow unresolved evars (this is the behaviour of [eelim]).
    - [clear]: if [Some _], [clear] tells whether to remove [t] from the context.
      If [None] we use the default clear flag.
    - [eliminator]: if [Some _] we use this as the eliminator for [t].
      If [None] we use the default eliminator associated to [t]. *)
val elim :
  evars_flag -> clear_flag -> constr with_bindings -> constr with_bindings option -> unit Proofview.tactic

(** Variant of [elim] which uses the default eliminator. *)
val default_elim : evars_flag -> clear_flag -> constr with_bindings ->
  unit Proofview.tactic

val general_elim_clause : evars_flag -> unify_flags -> Id.t option ->
    ((metavariable list * Unification.Meta.t) * EConstr.t * EConstr.types) -> Constant.t -> unit Proofview.tactic

(** [general_case_analysis with_evars clear (t, bindings)] performs case analysis on [t].
    If [t] is a variable which is not in the context, we attempt to perform introductions
    until [t] is in the context.
    - [with_evars]: if [true] allow unsolved evars (this is the behaviour of [ecase]).
    - [clear]: if [Some _], [clear] tells whether to remove [t] from the context.
      If [None] we use the default clear flag. *)
val general_case_analysis : evars_flag -> clear_flag -> constr with_bindings -> unit Proofview.tactic

(** [simplest_case t] performs case analysis on [t]. It does not allow unresolved evars,
    and uses the default clear flag. *)
val simplest_case : constr -> unit Proofview.tactic

(** [exfalso] changes the conclusion to [False]. *)
val exfalso : unit Proofview.tactic

(** {6 Constructor tactics. } *)

(** [constructor_tac with_evars expected_num_ctors i bindings] checks that the goal is
    an inductive [ind] and applies the [i]-th constructor of [ind].
    - [with_evars]: if [true] applying the constructor can leave evars (this gives the
      behaviour of [econstructor]).
    - [expected_num_ctors]: if [Some nctors] we check that the number of constructors of [ind]
      is equal to [nctors].
    - [i]: index of the constructor to apply, starting at [1].
    - [bindings]: bindings to use when applying the constructor. *)
val constructor_tac : evars_flag -> int option -> int ->
  constr bindings -> unit Proofview.tactic

(** [one_constructor i bindings] is a specialization of [constructor_tac] with:
    - [with_evars] set to [false].
    - [expected_num_ctors] set to [None]. *)
val one_constructor : int -> constr bindings -> unit Proofview.tactic

(** [any_constructor with_evars tac] checks that the goal is an inductive [ind] and
    tries to apply the constructors of [ind] one by one (from first to last).
    - [with_evars]: if [true] applying the constructor can leave evars (this gives the
      behaviour of [econstructor]).
    - [tac]: we run [tac] after applying each constructor, and backtrack
      to the next constructor if [tac] fails. *)
val any_constructor : evars_flag -> unit Proofview.tactic option -> unit Proofview.tactic

(** [simplest_left] checks the goal is an inductive with two constructors
    and applies the first constructor. *)
val simplest_left : unit Proofview.tactic

(** Variant of [simplest_left] which takes bindings. *)
val left  : constr bindings -> unit Proofview.tactic

(** Variant of [simplest_left] which takes an evar flag and bindings. *)
val left_with_bindings : evars_flag -> constr bindings -> unit Proofview.tactic

(** [simplest_right] checks the goal is an inductive with two constructors
    and applies the second constructor. *)
val simplest_right : unit Proofview.tactic

(** Variant of [simplest_right] which takes bindings. *)
val right : constr bindings -> unit Proofview.tactic

(** Variant of [simplest_right] which takes an evar flag and bindings. *)
val right_with_bindings : evars_flag -> constr bindings -> unit Proofview.tactic

(** [simplest_left] checks the goal is an inductive with one constructor
    and applies the (unique) constructor. *)
val simplest_split : unit Proofview.tactic

(** Variant of [simplest_split] which takes bindings. *)
val split : constr bindings -> unit Proofview.tactic

(** Variant of [simplest_split] which takes an evar flag and bindings. *)
val split_with_bindings : evars_flag -> constr bindings list -> unit Proofview.tactic

(** Variant of [simplest_split] which takes an evar flag and delayed bindings. *)
val split_with_delayed_bindings : evars_flag -> constr bindings delayed_open list -> unit Proofview.tactic

(** {6 Equality tactics. } *)

(** Hook to the [setoid_reflexivity] tactic, set at runtime. *)
val setoid_reflexivity : unit Proofview.tactic Hook.t

(** [reflexivity_red reduce] solves a goal of the form [x = y].
    - [reduce]: if [true] we weak-head normalize the goal before checking it is
      indeed an equality. *)
val reflexivity_red : bool -> unit Proofview.tactic

(** Variant of [reflexivity_red] which does not perform reduction,
    and falls back to [setoid_reflexivity] in case of failure. *)
val reflexivity : unit Proofview.tactic

(** [intros_reflexivity] performs [intros] followed by [reflexivity]. *)
val intros_reflexivity : unit Proofview.tactic

(** Hook to the [setoid_symmetry] tactic, set at runtime. *)
val setoid_symmetry : unit Proofview.tactic Hook.t

(** [symmetry_red reduce] checks the goal is of the form [x = y] and changes it to [y = x].
    - [reduce]: if [true] we weak-head normalize the goal before checking it is
      indeed an equality. *)
val symmetry_red : bool -> unit Proofview.tactic

(** Variant of [symmetry_red] which does not perform reduction,
    and falls back to [setoid_symmetry] in case of failure. *)
val symmetry : unit Proofview.tactic

(** Hook to the [setoid_symmetry_in] tactic, set at runtime. *)
val setoid_symmetry_in : (Id.t -> unit Proofview.tactic) Hook.t

(** [intros_symmetry clause] performs [intros] followed by [symmetry] on all
    the locations indicated by [clause] (i.e. the conclusion and/or a (subset of) hypotheses).
    Actual occurences contained in [clause] are not used: only the hypotheses names are relevant. *)
val intros_symmetry : clause -> unit Proofview.tactic

(** Hook to the [setoid_transitivity] tactic, set at runtime. *)
val setoid_transitivity : (constr option -> unit Proofview.tactic) Hook.t

(** [transitivity_red reduce t] checks the goal is of the form [x = y] and changes it to [x = t] and [t = y].
    - [reduce]: if [true] we weak-head normalize the goal before checking it is
      indeed an equality.
    - [t]: if [Some] then we use [apply eq_trans with t] to perform transitivity.
      If [None] we use [eapply eq_trans] instead. *)
val transitivity_red : bool -> constr option -> unit Proofview.tactic

(** Variant of [transitivity_red] which does not perform reduction,
    uses [apply eq_trans with t],
    and falls back to [setoid_transitivity] in case of failure. *)
val transitivity : constr -> unit Proofview.tactic

(** Variant of [transitivity_red] which does not perform reduction,
    uses [eapply eq_trans],
    and falls back to [setoid_transitivity] in case of failure. *)
val etransitivity : unit Proofview.tactic

(** [intros_transitivity t] performs [intros] followed by [transitivity t] or [etransivity t]
    (depending on whether [t] is [Some] or [None]). *)
val intros_transitivity : constr option -> unit Proofview.tactic

(** {6 Forward reasoning tactics. } *)

(** [assert_before x T] first asks to prove [T], then to prove the original goal augmented
    with a new hypothesis of type [x : T].
    - [x]: if [None] the name of the hypothesis is generated automatically.
      If [Some] then it is the name of the hypothesis (which should not be already defined in the context). *)
val assert_before : Name.t -> types -> unit Proofview.tactic

(** Variant of [assert_before] which allows replacing hypotheses. *)
val assert_before_replacing: Id.t -> types -> unit Proofview.tactic

(** [assert_after x T] first asks the original goal augmented with a new hypothesis of type [x : T],
    then to prove [T].
    - [x]: if [None] the name of the hypothesis is generated automatically.
      If [Some] then it is the name of the hypothesis (which should not be already defined in the context). *)
val assert_after : Name.t -> types -> unit Proofview.tactic

(** Variant of [assert_after] which allows replacing hypotheses. *)
val assert_after_replacing : Id.t -> types -> unit Proofview.tactic

(** [forward before by_tac ipat t] performs a forward reasoning step.
    - If [by_tac] is [None] it adds a new hypothesis with _body_ equal to [t].
    - If [by_tac] is [Some tac] it asks to prove [t] and to prove the original goal
      augmented with a new hypothesis of type [t]. If [tac] is [Some _] then [tac] is used
      to prove [t] (and [tac] is required to succeed).
    - [before]: if [true] then [t] must be proved first.
      If [false] then [t] must be proved [last]. *)
val forward : bool -> unit Proofview.tactic option option ->
    intro_pattern option -> constr -> unit Proofview.tactic

(** [assert_by x T tac] adds a new hypothesis [x : T]. The tactic [tac] is used
    to prove [T]. If [x] is [None] a fresh name is automatically generated. *)
val assert_by : Name.t -> types -> unit Proofview.tactic ->
  unit Proofview.tactic

(** [enough_by x T tac] changes the goal to [T]. The tactic [tac] is used to
    prove the orignal goal augmented with a hypothesis [x : T]. If [x] is [None] a fresh name
    is automatically generated. *)
val enough_by : Name.t -> types -> unit Proofview.tactic ->
  unit Proofview.tactic

(** [pose_proof x t] adds a new hypothesis [x := t]. If [x] is [None] a fresh name
    is automatically generated. *)
val pose_proof : Name.t -> constr -> unit Proofview.tactic

(** Implements the tactic [cut], actually a modus ponens rule. *)
val cut : types -> unit Proofview.tactic

(** [pose_tac x t] adds a new hypothesis [x := t]. If [x] is [None] a fresh name
    is automatically generated. Fails if there is alreay a hypothesis named [x]. *)
val pose_tac : Name.t -> constr -> unit Proofview.tactic

val letin_tac : (bool * intro_pattern_naming) option ->
  Name.t -> constr -> types option -> clause -> unit Proofview.tactic

(** Common entry point for user-level "set", "pose", and "remember". *)
val letin_pat_tac : evars_flag -> (bool * intro_pattern_naming) option ->
  Name.t -> (evar_map option * constr) -> clause -> unit Proofview.tactic

(** {6 Other tactics. } *)

val specialize_eqs : Id.t -> unit Proofview.tactic

val general_rewrite_clause :
  (bool -> evars_flag -> constr with_bindings -> clause -> unit Proofview.tactic) Hook.t

val subst_one :
  (bool -> Id.t -> Id.t * constr * bool -> unit Proofview.tactic) Hook.t

val declare_intro_decomp_eq :
  ((int -> unit Proofview.tactic) -> Rocqlib.rocq_eq_data * types *
   (types * constr * constr) ->
   constr * types -> unit Proofview.tactic) -> unit

(** Tactic analogous to the [Strategy] vernacular, but only applied
    locally to the tactic argument. *)
val with_set_strategy :
  (Conv_oracle.level * Names.GlobRef.t list) list -> 'a Proofview.tactic -> 'a Proofview.tactic

(** {6 Simple form of common tactics. } *)

module Simple : sig
  (** Simplified version of some of the above tactics *)

  val apply : constr -> unit Proofview.tactic
  val eapply : constr -> unit Proofview.tactic
  val elim : constr -> unit Proofview.tactic
  val case : constr -> unit Proofview.tactic
  val apply_in : Id.t -> constr -> unit Proofview.tactic

end

(** {6 Tacticals defined directly in term of Proofview} *)

(** [refine ~typecheck c] is [Refine.refine ~typecheck c]
    followed by beta-iota-reduction of the conclusion. *)
val refine : typecheck:bool -> (evar_map -> evar_map * constr) -> unit Proofview.tactic

(** The reducing tactic called after [refine]. *)
val reduce_after_refine : unit Proofview.tactic

(** {6 Internals, do not use} *)

module Internal :
sig

val explicit_intro_names : 'a intro_pattern_expr CAst.t list -> Id.Set.t

val check_name_unicity : env -> Id.t list -> Id.t list -> 'a intro_pattern_expr CAst.t list -> unit

val dest_intro_patterns : evars_flag -> Id.Set.t -> lident list ->
  Id.t Logic.move_location -> intro_patterns ->
  (Id.t list -> lident list -> unit Proofview.tactic) -> unit Proofview.tactic

end
