Require Import Ltac2.Ltac2 Ltac2.Control.
From Ltac2 Require Import Hints.

Ltac2 Type exn ::= [ Error ].

Parameter P : Prop.
Parameter p : P.

Create HintDb custom.
Hint Resolve p : custom.

Ltac2 custom_db () : hint_db :=
    match Hints.get_hint_db "custom" with
      | Some db => db
      | _ => throw Error
    end.

Goal P.
    Ltac2 myhint () : Hints.hint :=
        let hints := Hints.get_applicable_hints (custom_db ()) in
        List.nth hints 0.
    Hints.run_hint (myhint ()).
Qed.
