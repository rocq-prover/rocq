(* Test file for Printing Fully Qualified option *)

Module Foo.
  Axiom ax : False.
End Foo.

Module Bar.
  Axiom ax : False.
End Bar.

Definition use_foo := Foo.ax.
Definition use_bar := Bar.ax.

(* Default printing (shortest name) *)
Print use_foo.
Print use_bar.

(* Fully qualified printing *)
Set Printing Fully Qualified.
Print use_foo.
Print use_bar.

(* Test with nested modules *)
Module Outer.
  Module Inner.
    Definition def := 0.
  End Inner.
End Outer.

Definition use_nested := Outer.Inner.def.
Print use_nested.

Unset Printing Fully Qualified.
Print use_nested.
