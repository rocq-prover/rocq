Require Import Ltac2.Ltac2.

Fail Check $hyp:id.

Ltac2 Eval let id := @x in '(fun (x:nat) (x : bool) => eq_refl : (x, &x) = (x, $hyp:id)).

Fail Ltac2 Eval let id := @x in '$hyp:id.
Fail Ltac2 Eval let id := @x in '(fun x : nat => $hyp:id : bool).

Ltac2 Eval let id := @x in constr:(fun x => $hyp:id : nat).

Section S.
  Variable x : nat.

  Ltac2 Eval let id := @x in '(fun x : bool => eq_refl : (x, &x) = (x, $hyp:id)).

  Ltac2 Eval let id := @x in '($hyp:id : nat).
  Fail Ltac2 Eval let id := @x in '($hyp:id : bool).
End S.

Set Mangle Names.

Ltac2 Eval let id := @x in '(fun (x:nat) (x:bool) => eq_refl : &x = $hyp:id :> bool).

Ltac2 Eval let id := @_1 in '(fun (x:nat) (x:bool) => eq_refl : &_1 = $hyp:id :> nat).
