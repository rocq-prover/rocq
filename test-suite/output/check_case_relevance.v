From Ltac2 Require Import Ltac2 Constr.
Import Constr.Unsafe.

Ltac2 bad p i :=
  let badx := Binder.unsafe_make None Relevance.irrelevant 'nat in
  let br := make (Lambda badx (make (Lambda badx i))) in
  let ind := match reference:(prod) with Std.IndRef ind => ind | _ => Control.throw Assertion_failure end in
  make (Case (case ind) ('(fun (_:nat * nat) => nat), Relevance.relevant) NoInvert p [|br|]).

Fail Definition badfst (p:nat * nat) := ltac2:(let x := bad '&p (make (Rel 2)) in exact $x).

Ltac2 bad_dep p :=
  let x := Binder.unsafe_make (Some @x) Relevance.relevant 'nat in
  let e := Binder.unsafe_make (Some @e) Relevance.irrelevant (make (App 'eq [|'nat; make (Rel 1); '0|])) in
  let br := make (Lambda x (make (Lambda e (make (Rel 2))))) in
  let ind := match reference:(sigT) with Std.IndRef ind => ind | _ => Control.throw Assertion_failure end in
  make (Case (case ind) ('(fun (_:{x : nat & x = 0}) => nat), Relevance.relevant) NoInvert p [|br|]).

Fail Definition badprojT1 (p:{x : nat & x = 0}) := ltac2:(let c := bad_dep '&p in exact $c).
