Module Type WRAP.
  Parameter t : Set.
End WRAP.

Module Type PARAMS.
  Declare Module Arg : WRAP.
End PARAMS.

Module Type JOKER. (* also breaks if you remove `Type` *)
End JOKER.

Module Type COMBINED := PARAMS <+ JOKER. (* Fix 1: Remove `<+ JOKER` *)

Module Inst <: WRAP.
  Inductive t_ := Q | R. (* Fix 2: Move this definition away *)
  Definition t := t_.
End Inst.

Module Type RECOMBINED := COMBINED with Module Arg := Inst.

Module Type LOCK_DEFS(Mod : RECOMBINED). (* also breaks if you remove `Type` *)
  Goal Mod.Arg.t -> True.
    intros.
    (* Fix 3: run `destruct (H : Inst.t)` instead *)
    destruct H. (* Error: Anomaly "Uncaught exception Not_found." Please report at http://coq.inria.fr/bugs/. *)
    all: constructor.
  Qed.
End LOCK_DEFS.
