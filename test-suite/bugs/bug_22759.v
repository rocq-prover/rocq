Inductive J : Type := CJ : J -> J.
CoInductive Stream : Type := Cons : Stream -> Stream.

Fail Definition d (A := J) (B := Stream) :=
  fix F (y : nat) (x : B) {struct x} : False :=
    match x with Cons s => F y s end.

(* Definition bad : False := d 0 (cofix inf := Cons inf). *)
