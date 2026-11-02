Module Type OrderedType.
  Parameter Inline t : Type.
End OrderedType.

Module Type S.
  Parameter t : Type.
End S.

Module FSetHide (X : S).
  Include X.
End FSetHide.

Module PositiveSet.
  Definition t := forall x, x.
End PositiveSet.

Module NumSet := FSetHide PositiveSet.

Module IntMake (X: OrderedType).
 Module E := X.
End IntMake.

Module StateSetMap := IntMake NumSet.

Ltac k := unfold StateSetMap.E.t.

Goal PositiveSet.t.
Proof.
progress k.
Abort.
