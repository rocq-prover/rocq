
Definition fplus f g : nat -> nat := fun x => f x + g x.

Infix "+" := fplus : function_scope.

Check 0 + 0.

Check (S + S)%function 0.

Open Scope function_scope.

Arguments fplus _ _ {x}.

Check (S + S) (x:=(0+0)%nat).

Check (S + S) (x:=0+0)%nat.

(* previous command used to be parsed as the following: *)
Fail Check ((S + S) (x:=0+0))%nat.
