(* -*- coq-prog-args: ("-noinit") -*- *)
Inductive False : Prop := .
Inductive True : Prop := I.
Inductive eq (A : Type) (x : A) : forall (_ : A), Prop := eq_refl : eq A x x.

Set Universe Polymorphism.
Primitive int := #int63_type.
Primitive array := #array_type.
Primitive default : forall A (_ : array A), A := #array_default.
Unset Universe Polymorphism.

Module Type SIG.
  Parameter P : Prop.
  Inductive T : Prop := mk : forall (_ : P), T.
End SIG.

Module F (X : SIG).
  Definition eq_T : eq Prop X.T (default Prop [| | X.T : Prop |]) := eq_refl Prop X.T.
End F.

Module MTrue <: SIG.
  Definition P : Prop := True.
  Inductive T : Prop := mk : forall (_ : P), T.
End MTrue.

Module MFalse <: SIG.
  Definition P : Prop := False.
  Inductive T : Prop := mk : forall (_ : P), T.
End MFalse.

Module N1 := F MTrue.
Module N2 := F MFalse.

Check (N1.eq_T : eq Prop MTrue.T (default Prop [| | MTrue.T : Prop |])).
Check (N2.eq_T : eq Prop MFalse.T (default Prop [| | MFalse.T : Prop |])).
Fail Check (N1.eq_T : eq Prop MTrue.T (default Prop [| | MFalse.T : Prop |])).

Fail Definition boom : False :=
  let t_false : MFalse.T :=
    match N2.eq_T in (eq _ _ Z) return (forall (_ : Z), MFalse.T) with
    | eq_refl _ _ => fun x : MFalse.T => x
    end
      (match N1.eq_T in (eq _ _ Y) return Y with
       | eq_refl _ _ => MTrue.mk I
       end)
  in
  match t_false with
  | MFalse.mk p => p
  end.
