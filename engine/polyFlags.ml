type t = {
  univ_polymorphic : bool;
  implicit_sort_polymorphic : bool;
  cumulative : bool;
}

let make ~univ_polymorphic ~implicit_sort_polymorphic ~cumulative =
  if (implicit_sort_polymorphic || cumulative) && not univ_polymorphic then
    CErrors.user_err Pp.(str "Cannot have sort polymorphic or cumulative but not level polymorphic constructions");
  { implicit_sort_polymorphic; univ_polymorphic; cumulative }

let default = { implicit_sort_polymorphic = false; univ_polymorphic = false; cumulative = false }
let of_univ_poly b = { default with univ_polymorphic = b }

let implicit_sort_polymorphic x = x.implicit_sort_polymorphic
let univ_polymorphic x = x.univ_polymorphic
let cumulative x = x.cumulative

(* Used to have distinguished default behaviors when treating assumptions/axioms, definitions or inductives *)
type assumption_or_definition =
  Assumption | Definition | Inductive
