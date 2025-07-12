Record type := Pack {sort : Type}.
Record def (T : type) := Def { r : sort T }.
Canonical mkdef (xt : type) (x : sort xt) := Def xt x.

Axiom t : type.
Axiom f : sort t -> sort t.

Canonical fdef (x : def t) := Def t (f (r t x)).

Axiom myeq0 : forall (x : def t), r t x = r t x.

Require Import ssreflect.
Goal (fun x : sort t => f x) = (fun x : sort t => x).
Fail rewrite myeq0.
(* Anomaly "in retyping: unbound local variable." *)
Abort.
