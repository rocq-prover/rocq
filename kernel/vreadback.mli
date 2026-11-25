(** Typed readback of VM values. *)

type context = {
  evars : CClosure.evar_handler;
  (** Number of captured hypotheses and the type abstracted over them (in
      VM argument order). Only called when reading back an unresolved evar. *)
  evar_type : Evar.t -> int * Constr.types;
  return_is_relevant : Environ.env -> Sorts.relevance -> bool;
}

val readback : normalize_params:bool -> Environ.env -> context ->
  Vmvalues.values -> Constr.types -> Constr.constr

(** Read back a value known to represent a type. *)
val readback_type : Environ.env -> context -> Vmvalues.values -> Constr.types
