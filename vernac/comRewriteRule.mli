val do_symbols : poly:bool -> unfold_fix:bool ->
  (Vernacexpr.coercion_flag * ((Names.lident * Constrexpr.poly_decl_expr option) list * Constrexpr.constr_expr)) list
  -> unit

val do_rules :
  Names.Id.t ->
  (Constrexpr.poly_decl_expr option * Constrexpr.constr_expr * Constrexpr.constr_expr) list ->
  unit
