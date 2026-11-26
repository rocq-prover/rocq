Declare ML Module "rocq-runtime.plugins.funind".

Class Monoid {A : Type} (dot : A -> A -> A) (one : A) :=
  {
    dot_assoc a b c : dot (dot a b) c = dot a (dot b c);
    unit_left a : dot one a = a;
    unit_right a : dot a one = a
  }.

Generalizable Variables A dot one.

Fail Function binary_power_mult `{Monoid A dot one} (acc x:A)(n:nat){measure (fun i=>i) n} : A :=
  match n with
    0%nat => acc
  | _ => if  Nat.even n
         then binary_power_mult  acc (dot x x) (Nat.div2 n)
         else binary_power_mult  (dot acc  x) (dot  x  x) (Nat.div2 n)
  end.
