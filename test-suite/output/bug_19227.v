Inductive T (a := 0) : nat -> Set := C : T 0.

Definition test (x : T 0) := match x in T e return e = e with C => eq_refl end.

Print test.
(* was
test =
fun x : T 0 =>
match x in (@T _ _ e) return (e = e) with
| C _ => eq_refl
end
     : T 0 -> 0 = 0

Arguments test x
*)
