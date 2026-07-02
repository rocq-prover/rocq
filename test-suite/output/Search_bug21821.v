Section K.
Axiom X : Type.
Parameter X2 : Type.
Hypothesis Y : Type.
Variable Y2 : Type.

Search is:Axiom.
  (* Shows "X: Type" *)
Search is:Parameter.
  (* Shows "X2: Type" *)
Search is:Hypothesis.
  (* Should show "Y: Type"*)
Search is:Variable.
  (* Should show "Y2: Type"*)

End K.
