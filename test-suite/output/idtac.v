(* Printing all kinds of Ltac generic arguments *)

Tactic Notation "myidtac" string(v) := idtac v.
Goal True.
Proof.
myidtac "foo".
Abort.

Tactic Notation "myidtac2" ref(c) := idtac c.
Goal True.
Proof.
myidtac2 True.
Abort.

Tactic Notation "myidtac3" preident(s) := idtac s.
Goal True.
Proof.
myidtac3 foo.
Abort.

Tactic Notation "myidtac4" int_or_var(n) := idtac n.
Goal True.
Proof.
myidtac4 3.
Abort.

Tactic Notation "myidtac5" ident(id) := idtac id.
Goal True.
Proof.
myidtac5 foo.
Abort.

(* Checking non focussing of idtac for integers *)
Goal True/\True.
Proof.
split.
all:let c:=numgoals in idtac c.
Abort.

(* Checking printing of lists and its focussing *)
Tactic Notation "myidtac6" constr_list(l) := idtac "<" l ">".
Goal True/\True.
Proof.
split.
all:myidtac6 True False Prop.
(* An empty list is focussing because of interp_genarg of a constr *)
(* even if it is not focussing on printing *)
all:myidtac6.
Abort.

Tactic Notation "myidtac7" int_list(l) := idtac "<<" l ">>".
Goal True/\True.
Proof.
split.
all:myidtac7 1 2 3.
Abort.
