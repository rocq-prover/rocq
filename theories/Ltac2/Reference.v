Require Import Ltac2.Init.
Require Ltac2.Std Ltac2.Ident Ltac2.Ind Ltac2.Constructor Ltac2.Constant.

Ltac2 Type t := Std.reference.
Import Ltac2.Std.

Ltac2 equal r1 r2 :=
match r1, r2 with
| VarRef i1, VarRef i2 => Ident.equal i1 i2
| ConstRef c1, ConstRef c2 => Constant.equal c1 c2
| IndRef ind1, IndRef ind2 => Ind.equal ind1 ind2
| ConstructRef cstr1, ConstructRef cstr2 => Constructor.equal cstr1 cstr2
| _, _ => false
end.
