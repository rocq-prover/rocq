From Ltac2 Require Import Ltac2.

Import Module.Notations.

(* can't use assert because it's a notation... *)
Ltac2 check := Control.assert_true.

Ltac2 to_string m := Message.to_string (Module.to_message m).

Fail Ltac2 Eval module:(Ltac2.init).

Ltac2 Eval check (Module.equal module:(Init) module:(Ltac2.Init)).

Ltac2 Eval check (Bool.neg (Module.equal module:(Ltac1) module:(Init))).

Ltac2 Eval check (Bool.neg (Module.equal module:(Ltac2.Notations) module:(Ltac2.Module.Notations))).

(* nametab based printing, and files are available unqualified (if no conflicts) *)
Ltac2 Eval check (String.equal (to_string module:(Ltac2.Constr)) "Constr").

(* current file *)
Ltac2 Eval check (String.equal (to_string module:(modules)) "modules").

Ltac2 Eval check (Bool.neg (Module.is_open module:(Ltac2.Init))).
Ltac2 Eval check (Module.is_library module:(Ltac2.Init)).
Ltac2 Eval check (Bool.neg (Module.is_modtype module:(Ltac2.Init))).
Ltac2 Eval check (Bool.neg (Module.is_functor module:(Ltac2.Init))).
Ltac2 Eval check (Bool.neg (Module.is_bound_module module:(Ltac2.Init))).

Ltac2 Eval check (Module.is_open module:(modules)).
Ltac2 Eval check (Module.is_library module:(modules)).
Ltac2 Eval check (Bool.neg (Module.is_modtype module:(modules))).
Ltac2 Eval check (Bool.neg (Module.is_functor module:(modules))).
Ltac2 Eval check (Bool.neg (Module.is_bound_module module:(modules))).

Ltac2 Eval check (Option.is_none (Module.parent_module module:(modules))).

Ltac2 Eval check (Module.equal (Module.current_module()) module:(modules)).

(* not checking the full list to make this test more stable *)
Ltac2 Eval check
  (Option.equal Module.equal
     (List.last_opt (Module.loaded_libraries ()))
     (Some module:(Ltac2.Ltac2))).

Ltac2 Eval check
  (List.mem Module.equal module:(Ltac2.Init) (Module.loaded_libraries())).

Ltac2 Eval check
  (List.mem Module.equal module:(Prelude) (Module.loaded_libraries())).

Module Field.
  Import Module.Field.
  Import Std.

  Ltac2 Type t := [ Submodule (Module.t) | Ref (reference) | Rewrule (Module.Field.rewrule) ].

  (* XXX move to Std? or new Reference module?? *)
  Ltac2 ref_equal a b :=
    match a, b with
    | VarRef a, VarRef b => Ident.equal a b
    | ConstRef a, ConstRef b => Constant.equal a b
    | IndRef a, IndRef b => Ind.equal a b
    | ConstructRef a, ConstructRef b => Constructor.equal a b
    | (VarRef _ | ConstRef _ | IndRef _ | ConstructRef _), _ => false
    end.

  Ltac2 equal a b :=
    match a, b with
    | Submodule a, Submodule b => Module.equal a b
    | Ref a, Ref b => ref_equal a b
    | Rewrule _, Rewrule _ => Control.throw_invalid_argument "rewrule not tested here"
    | (Submodule _ | Ref _ | Rewrule _), _ => false
    end.

  Ltac2 to_adt f :=
    Module.Field.handle f {
        handle_submodule := (fun m => Submodule m);
        handle_reference := (fun r => Ref r);
        handle_rewrule := (fun r => Rewrule r);
      }.
End Field.
Import Field.

Ltac2 contents m := Option.map (List.map Field.to_adt) (Module.module_contents m).

Ltac2 contents_equal a b := Option.equal (List.equal Field.equal) a b.

Module Type T1.
  Module T1_M.
    Parameter x : nat.

    Ltac2 Eval check (Module.is_open module:(T1)).
    Ltac2 Eval check (Module.is_modtype module:(T1)).
    Ltac2 Eval check (Bool.neg (Module.is_functor module:(T1))).
    Ltac2 Eval check (Bool.neg (Module.is_bound_module module:(T1))).
    Ltac2 Eval check (Bool.neg (Module.is_library module:(T1))).

    Ltac2 Eval check (Module.is_open module:(T1_M)).
    Ltac2 Eval check (Bool.neg (Module.is_modtype module:(T1_M))).
    Ltac2 Eval check (Bool.neg (Module.is_functor module:(T1_M))).
    Ltac2 Eval check (Bool.neg (Module.is_bound_module module:(T1_M))).
    Ltac2 Eval check (Bool.neg (Module.is_library module:(T1_M))).

    Ltac2 Eval check (Module.equal (Option.get (Module.parent_module module:(T1_M))) module:(T1)).
    Ltac2 Eval check (Module.equal (Module.module_of_reference reference:(x)) module:(T1_M)).

    Ltac2 Eval check (Module.equal (Module.current_module()) module:(T1_M)).

    Ltac2 Eval check
      (contents_equal
         (contents module:(T1))
         (Some [Submodule module:(T1_M)])).

    Ltac2 Eval check
      (contents_equal
         (contents module:(T1_M))
         (Some [Ref reference:(x)])).

  End T1_M.

  Definition xx := T1_M.x.

  Ltac2 Eval check (Module.is_open module:(T1)).
  Ltac2 Eval check (Module.is_modtype module:(T1)).
  Ltac2 Eval check (Bool.neg (Module.is_functor module:(T1))).
  Ltac2 Eval check (Bool.neg (Module.is_bound_module module:(T1))).
  Ltac2 Eval check (Bool.neg (Module.is_library module:(T1))).

  Ltac2 Eval check (Bool.neg (Module.is_open module:(T1_M))).
  Ltac2 Eval check (Bool.neg (Module.is_modtype module:(T1_M))).
  Ltac2 Eval check (Bool.neg (Module.is_functor module:(T1_M))).
  Ltac2 Eval check (Bool.neg (Module.is_bound_module module:(T1_M))).
  Ltac2 Eval check (Bool.neg (Module.is_library module:(T1_M))).

  Ltac2 Eval check (Module.equal (Module.current_module()) module:(T1)).

  Ltac2 Eval check
    (contents_equal
       (contents module:(T1))
       (Some [Submodule module:(T1_M);
              Ref reference:(xx)])).

  Ltac2 Eval check
    (contents_equal
       (contents module:(T1_M))
       (Some [Ref reference:(T1_M.x)])).

End T1.

Ltac2 Eval check (Bool.neg (Module.is_open module:(T1))).
Ltac2 Eval check (Module.is_modtype module:(T1)).
Ltac2 Eval check (Bool.neg (Module.is_functor module:(T1))).
Ltac2 Eval check (Bool.neg (Module.is_bound_module module:(T1))).
Ltac2 Eval check (Bool.neg (Module.is_library module:(T1))).

Fail Ltac2 Eval module:(T1.T1_M).

Ltac2 Eval check (contents_equal (contents module:(T1)) None).

Module Sub1.
  Module F1 (X:T1).
    Definition double := X.T1_M.x + X.T1_M.x.

    Ltac2 Eval check (Module.is_open module:(F1)).
    Ltac2 Eval check (Bool.neg (Module.is_modtype module:(F1))).
    Ltac2 Eval check (Module.is_functor module:(F1)).
    Ltac2 Eval check (Bool.neg (Module.is_bound_module module:(F1))).
    Ltac2 Eval check (Bool.neg (Module.is_library module:(F1))).

    Ltac2 Eval check (Bool.neg (Module.is_open module:(X))).
    Ltac2 Eval check (Bool.neg (Module.is_modtype module:(X))).
    Ltac2 Eval check (Bool.neg (Module.is_functor module:(X))).
    Ltac2 Eval check (Module.is_bound_module module:(X)).
    Ltac2 Eval check (Bool.neg (Module.is_library module:(X))).

    Ltac2 Eval check (Bool.neg (Module.is_open module:(X.T1_M))).
    Ltac2 Eval check (Bool.neg (Module.is_modtype module:(X.T1_M))).
    Ltac2 Eval check (Bool.neg (Module.is_functor module:(X.T1_M))).
    Ltac2 Eval check (Bool.neg (Module.is_bound_module module:(X.T1_M))).
    Ltac2 Eval check (Bool.neg (Module.is_library module:(X.T1_M))).

    Ltac2 Eval check (Option.is_none (Module.parent_module module:(X))).

    Ltac2 Eval check
      (contents_equal
         (contents module:(Sub1))
         (Some [Submodule module:(F1)])).

    Ltac2 Eval check
      (contents_equal
         (contents module:(F1))
         (Some [Ref reference:(double)])).

    Ltac2 Eval check
      (contents_equal
         (contents module:(X))
         (Some [Submodule module:(X.T1_M); Ref reference:(X.xx)])).

  End F1.

  Definition foo := 42.

  Ltac2 Eval check (Bool.neg (Module.is_open module:(F1))).
  Ltac2 Eval check (Bool.neg (Module.is_modtype module:(F1))).
  Ltac2 Eval check (Module.is_functor module:(F1)).
  Ltac2 Eval check (Bool.neg (Module.is_bound_module module:(F1))).
  Ltac2 Eval check (Bool.neg (Module.is_library module:(F1))).

  Ltac2 Eval check (contents_equal (contents module:(F1)) None).

End Sub1.
