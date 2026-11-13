(* The forged copy gives the module type U the label T, a second use of a
   label among the modules and module types. The environment then keeps
   the last module type labelled T, which is U. *)

Unset Elimination Schemes.

Inductive unit : Set := tt.

Module Type T.
  Parameter t : Set.
End T.

Module Type U.
  Parameter u : unit.
End U.
