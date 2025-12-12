type t = {
  univ_poly : bool;
  collapse_sort_variables : bool;
  cumulative : bool;
}

let make ~univ_poly ~collapse_sort_variables ~cumulative =
  if cumulative && not univ_poly then
    CErrors.user_err Pp.(str "Cannot have cumulative but not universe polymorphic constructions");
  if not collapse_sort_variables && not univ_poly then
    CErrors.user_err Pp.(str "Sort metavariables must be collapsed to Type in universe monomorphic constructions");
  { collapse_sort_variables; univ_poly; cumulative }

let default = { collapse_sort_variables = true; univ_poly = false; cumulative = false }
let of_univ_poly b = { default with univ_poly = b }

let collapse_sort_variables x = x.collapse_sort_variables
let univ_poly x = x.univ_poly
let cumulative x = x.cumulative

(* Used to have distinguished default behaviors when treating assumptions/axioms, definitions or inductives *)
type assumption_or_definition =
  Assumption | Definition | Inductive
