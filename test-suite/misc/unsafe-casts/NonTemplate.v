Declare ML Module "unsafe_cast.plugin".

(* Control for Template.v: this already requires the checker plugin. *)
#[universes(template=no)]
Inductive non_template_cast (A : (Type <:["test.accept"] Type)) : Type :=
  non_template_constructor : non_template_cast A.
