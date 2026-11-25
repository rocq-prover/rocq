Set Universe Polymorphism.

Definition choose@{q;u|} (A : Univ@{q;u}) (a b : A) (c : bool) : A :=
  match c with true => a | false => b end.

(* With an unknown scrutinee, the VM has to read back a suspended switch.
   Use the same bytecode at relevant, irrelevant and abstract qualities. *)
Definition choose_type (A : Set) (a b : A) (c : bool) :=
  Eval vm_compute in choose@{Type;Set} A a b c.
Definition choose_sprop (A : SProp) (a b : A) (c : bool) :=
  Eval vm_compute in choose@{SProp;Set} A a b c.
Definition choose_poly@{q;u|} (A : Univ@{q;u}) (a b : A) (c : bool) :=
  Eval vm_compute in choose@{q;u} A a b c.

Definition countdown@{q;u|} (A : Univ@{q;u}) (a : A) :=
  fix loop (n : nat) : A := match n with O => a | S m => loop m end.

Definition countdown_type (A : Set) (a : A) :=
  Eval vm_compute in countdown@{Type;Set} A a.
Definition countdown_sprop (A : SProp) (a : A) :=
  Eval vm_compute in countdown@{SProp;Set} A a.
Definition countdown_poly@{q;u|} (A : Univ@{q;u}) (a : A) :=
  Eval vm_compute in countdown@{q;u} A a.

CoInductive stream@{q;u|} (A : Univ@{q;u}) : Univ@{q;u} :=
| cons : A -> stream A -> stream A.

CoFixpoint repeat@{q;u|} (A : Univ@{q;u}) (a : A) : stream A :=
  cons A a (repeat A a).

Definition repeat_type (A : Set) (a : A) :=
  Eval vm_compute in repeat@{Type;Set} A a.
Definition repeat_sprop (A : SProp) (a : A) :=
  Eval vm_compute in repeat@{SProp;Set} A a.
Definition repeat_poly@{q;u|} (A : Univ@{q;u}) (a : A) :=
  Eval vm_compute in repeat@{q;u} A a.
