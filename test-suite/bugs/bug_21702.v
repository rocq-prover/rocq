(* Regression test for check_with_def universe constraint dropping bug.
   Bug: mod_typing.ml stored with Definition result using the WITH body's
   (weaker) universe constraints instead of the spec's (stronger) constraints.
   This allowed creating a coerce function Type@{u} -> Type@{v} with no
   constraint between u and v, leading to a proof of False via Girard's paradox. *)

Set Universe Polymorphism.

Module Type SIG.
  Section S.
    Universe u v.
    Constraint u <= v.
    Parameter coerce@{} : Type@{u} -> Type@{v}.
  End S.
End SIG.

(* The identity function satisfies coerce's type only when u <= v.
   The bug dropped this constraint from the result. *)
Module Type SIG2 := SIG with Definition coerce@{u v} := fun (x : Type@{u}) => x.
Declare Module M : SIG2.

(* After the fix, M.coerce should retain the Type@{u} -> Type@{u} type.
   Therefore, using it to push Type@{u} into a smaller universe should fail. *)
Section Test.
  Universe big small.
  Constraint small < big.

  (* This should fail: M.coerce@{big+1, small} would require big+1 <= small,
     but we have small < big, contradiction. *)
  Fail Definition A : Type@{small} := M.coerce Type@{big}.
End Test.
