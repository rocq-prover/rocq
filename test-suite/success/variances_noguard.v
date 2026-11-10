(* Variance inference must not unfold (co)fixpoints when guard checking is off: the
   unfolding of these unguarded fixpoints does not terminate (from MetaRocq's tmFix) *)
Set Universe Polymorphism.

Unset Guard Checking.
Definition loop {A B : Type} (f : (A -> option B) -> (A -> option B)) : A -> option B
  := (fix g (dummy : unit) {struct dummy} : A -> option B := f (fun a => g tt a)) tt.

CoInductive stream (A : Type) := Cons : A -> stream A -> stream A.

Definition coloop {A : Type} (f : stream A -> stream A) : stream A
  := (cofix g (dummy : unit) : stream A := f (g dummy)) tt.
Set Guard Checking.
