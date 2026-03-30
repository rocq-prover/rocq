Module M1. Module M2.
  Definition x := 1.
  Parameter z : unit.
End M2. End M1.

#[abbreviation]
  Module X := M1.M2.

Check eq_refl : X.z = M1.M2.z.

Module Type T. Parameter x : nat. End T.
Module F(A:T). Definition y := A.x + A.x. End F.

Module Y := F X.

Check eq_refl : Y.y = 2.

Module Type T1.
  Declare Module Inner : T.
End T1.

Module Outer1 : T1.
  Module Inner := X.
End Outer1.

Module Outer2.
  #[abbreviation] Module Inner := X.
End Outer2.
Fail Module OuterTest : T1 := Outer2.

Section S.
  #[abbreviation,global] Module X2 := X.
End S.

Module X3 := X2.
