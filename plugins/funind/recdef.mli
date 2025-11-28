open Constr

val tclUSER_if_not_mes :
     unit Proofview.tactic
  -> bool
  -> Names.Id.t list option
  -> unit Proofview.tactic

val recursive_definition :
  Summary.Interp.mut
  -> interactive_proof:bool
  -> is_mes:bool
  -> Names.Id.t
  -> Constrintern.internalization_env
  -> Constrexpr.constr_expr
  -> Constrexpr.constr_expr
  -> int
  -> Constrexpr.constr_expr
  -> (Summary.Interp.mut
      -> pconstant
      -> Indfun_common.tcc_lemma_value ref
      -> pconstant
      -> pconstant
      -> int
      -> EConstr.types
      -> int
      -> EConstr.constr
      -> unit)
  -> Constrexpr.constr_expr list
  -> Declare.Proof.t option
