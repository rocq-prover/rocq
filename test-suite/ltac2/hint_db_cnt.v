Require Import Ltac2.Ltac2 Ltac2.Control.
From Ltac2 Require Import Hints.

Ltac2 Type exn ::= [ Error ].

Parameter P : Prop.
Parameter p1 p2  : P.

Parameter Q : Prop.
Parameter q1 q2 : Q.

Create HintDb custom.
Hint Resolve p1 p2 q1 q2: custom.

Ltac2 custom_db () : hint_db :=
    match Hints.get_hint_db "custom" with
      | Some db => db
      | _ => throw Error
    end.

Goal P.
    let hints := Hints.get_applicable_hints (custom_db ()) in
    let hint_cnt := List.length hints in
    if Int.equal hint_cnt 2 then () else throw Error.
Abort.
