type t
(** Set of flags for universe level polymorphism, implicit sort polymorphism and cumulativity.
   Note that implicit sort polymorphism and cumulativity only make sense for constructions
   that are already level polymorphic. This invariant is ensured by the smart constructor below.
 *)

(** Raises a user error if [implicit_sort_polymorphic] or [cumulative] is true but [level_polymorphic] isn't *)
val make : level_polymorphic:bool -> implicit_sort_polymorphic:bool -> cumulative:bool -> t

(** All [false] *)
val default : t

(** Only sets the universe [level_polymorphism] flag.
    Use with care, this probably indicates that the code does not handle
    [cumulative] constructions when it should. Code relying on elaboration should
    also support the [implicit_sort_polymorphic] flag. *)
val of_level_poly : bool -> t

(** Accessors *)
val level_polymorphic : t -> bool
val implicit_sort_polymorphic : t -> bool
val cumulative : t -> bool

(** Alias of level_polymorphic. This can be used to decide if polymorphism is active or not.
  Use with care. *)
val is_polymorphic : t -> bool

(** Used to have distinguished default behaviors when treating assumptions/axioms,
    definitions or inductives *)
type assumption_or_definition =
  Assumption | Definition | Inductive
