Inductive RT := RTC (l : list RT).

#[warnings="-non-full-mutual"]
Fixpoint on_RT (rt : RT) : unit :=
  match rt with RTC l => on_list l end
with on_list (l : list RT) : unit :=
  tt.
