(* About on an abbreviation should mention the scopes of its arguments. *)

Abbreviation double x := (x + x).
About double.

Abbreviation add3 x y z := (x + y + z).
About add3.

(* A scope is also known for a type argument. *)
Abbreviation idp A := (fun a : A => a).
About idp.

(* Nothing is printed when there is no argument. *)
Abbreviation zero := 0.
About zero.
