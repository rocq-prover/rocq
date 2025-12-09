open Names

val declare_definition :
  Summary.Interp.mut -> poly:bool -> Id.t -> Evd.evar_map -> EConstr.t -> Names.GlobRef.t
