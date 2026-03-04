Require Import PrimArray.

Set Universe Polymorphism.

Definition foo@{u} := [| | nat |]@{u}.

Definition bar@{u v} := Eval lazy head in foo@{v}.
(* The term "Set" has type "Type@{Set+1}" while it is expected to have type "Type@{Var(0)}". *)
