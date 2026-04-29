(* from #20508 *)

#[universes(polymorphic=yes)]
Definition abc@{s;u|} := Type@{s;u}.
Inductive SUnit : SProp := stt.
Definition xyz : abc := SUnit. (* works as expected, abc is sort-polymorphic *)
Set Printing Universes.
Check @abc.
(* prints abc@{Type | test.294} : Type@{test.294+1} *)
