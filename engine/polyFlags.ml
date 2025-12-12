type t = {
  univ_polymorphic : bool;
  collapse_sorts_to_type : bool;
  cumulative : bool;
}

let make ~univ_polymorphic ~collapse_sorts_to_type ~cumulative =
  if cumulative && not univ_polymorphic then
    CErrors.user_err Pp.(str "Cannot have cumulative but not universe polymorphic constructions");
  if not collapse_sorts_to_type && not univ_polymorphic then
    CErrors.user_err Pp.(str "Sort metavariables must be collapsed to Type in universe monomorphic constructions");
  { collapse_sorts_to_type; univ_polymorphic; cumulative }

let default = { collapse_sorts_to_type = true; univ_polymorphic = false; cumulative = false }
let of_univ_poly b = { default with univ_polymorphic = b }

let collapse_sorts_to_type x = x.collapse_sorts_to_type
let univ_polymorphic x = x.univ_polymorphic
let cumulative x = x.cumulative

(* Used to have distinguished default behaviors when treating assumptions/axioms, definitions or inductives *)
type assumption_or_definition =
  Assumption | Definition | Inductive
