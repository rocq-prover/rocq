Inductive equal T (x : T) : T -> Type := Equal : equal T x x.

Goal forall a b, equal nat a b -> a  = b.
Proof.
  intros a b H.
  eassert (equal_rew : _) by abstract exact (fun (T : Type) (x : T) (P : T -> Type)
  (f : P x) (t : T) (e : equal T x t) =>
match e in (equal _ _ t0) return (P t0) with
| Equal _ _ => f
end).
  eassert (equal_rew_r : _) by abstract exact (fun (T : Type@{equal.u0}) (x y : T) (P : T -> Type)
  (HC : P y) (X : equal T x y) =>
match X in (equal _ _ y0) return (P y0 -> P x) with
| Equal _ _ => fun HC0 : P x => HC0
end HC).
Abort.
