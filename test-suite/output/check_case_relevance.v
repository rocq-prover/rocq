From Ltac2 Require Import Ltac2 Constr.
Import Constr.Unsafe.

Ltac2 bad p i :=
  let badx := Binder.unsafe_make None Relevance.irrelevant 'nat in
  let br := make (Lambda badx (make (Lambda badx i))) in
  let ind := match reference:(prod) with Std.IndRef ind => ind | _ => Control.throw Assertion_failure end in
  make (Case (case ind) ('(fun (_:nat * nat) => nat), Relevance.relevant) NoInvert p [|br|]).

Fail Definition badfst (p:nat * nat) := ltac2:(let x := bad '&p (make (Rel 2)) in exact $x).
