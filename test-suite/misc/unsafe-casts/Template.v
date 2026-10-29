Declare ML Module "unsafe_cast.plugin".

(* The standalone checker must check the original parameter type before
   reconstructing its template arity, even though reconstruction erases casts. *)
#[universes(template)]
Inductive template_cast (A : (Type <:["test.accept"] Type)) : Type :=
  template_constructor : template_cast A.
