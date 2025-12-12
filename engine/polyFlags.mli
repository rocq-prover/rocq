type t
(** Set of flags for universe polymorphism, implicit sort polymorphism and cumulativity.
    Note that implicit sort polymorphism (not collapsing sort variables to Type) and
    cumulativity only make sense for constructions that are already polymorphic.
    This invariant is ensured by the smart constructor below.
 *)

(** Raises a user error if [univ_poly = false] and either [collapse_sort_variables = false] or [cumulative = true]. *)
val make : univ_poly:bool -> collapse_sort_variables:bool -> cumulative:bool -> t

(** The [default] is monomorphic:
    [univ_poly] and [cumulative] are [false], [collapse_sort_variables] is [true] *)
val default : t

(** Only sets the universe [univ_poly] flag.
    Use with care, this probably indicates that the code does not handle
    [cumulative] constructions when it should. Code relying on elaboration should
    also support the [collapse_sort_variables] flag. *)
val of_univ_poly : bool -> t

(** Accessors *)
val univ_poly : t -> bool
val collapse_sort_variables : t -> bool
val cumulative : t -> bool

(** Used to have distinguished default behaviors when treating assumptions/axioms,
    definitions or inductives *)
type assumption_or_definition =
  Assumption | Definition | Inductive
