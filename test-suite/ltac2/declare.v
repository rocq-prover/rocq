Require Import Ltac2.Ltac2.
Require Import Ltac2.Definition.

Ltac2 get_name () : ident :=
  Option.get (Ident.of_string "some_name").

Ltac2 tp () : constr option :=
  Some constr:(nat).

Ltac2 body () : constr :=
  constr:(1 + 1).

Ltac2 d () : definition list :=
  [Defn false (get_name ()) (tp ()) (body ())].

Ltac2 Declare d ().

Definition y : nat := some_name.

Ltac2 Declare [Defn true (Option.get (Ident.of_string "some_other_name")) (tp ()) (body ())].

Definition z : nat := some_other_name.
