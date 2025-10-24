Require Import ListDef.

Fail Fixpoint test (l:list nat) {measure (length l)} : list nat :=
match l with
| nil => nil
| e::f => test f
end.
