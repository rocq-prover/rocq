open Names

val declare_definition :
  poly:PolyFlags.t -> Id.t -> Evd.evar_map -> EConstr.t -> Names.GlobRef.t
