type t
(** Set of flags for universe polymorphism, implicit sort polymorphism and cumulativity.
   Note that implicit sort polymorphism and cumulativity only make sense for constructions
   that are already polymorphic. This invariant is ensured by the smart constructor below.
 *)

(** Raises a user error if [collapse_sort_variables] or [cumulative] is true but [univ_poly] isn't *)
val make : univ_poly:bool -> collapse_sort_variables:bool -> cumulative:bool -> t

(** All [false] *)
val default : t

(** Only sets the universe [level_polymorphism] flag.
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
