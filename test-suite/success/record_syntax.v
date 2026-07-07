Module A.

Record Foo := { foo : unit; bar : unit }.

Definition foo_ := {|
  foo := tt;
  bar := tt
|}.

Definition foo0 (p : Foo) := match p with {| |} => tt end.
Definition foo1 (p : Foo) := match p with {| foo := f |} => f end.
Definition foo2 (p : Foo) := match p with {| foo := f; |} => f end.
Definition foo3 (p : Foo) := match p with {| foo := f; bar := g |} => (f, g) end.
Definition foo4 (p : Foo) := match p with {| foo := f; bar := g; |} => (f, g) end.

End A.

Module B.

Record Foo := { }.

End B.

Module C.

Record Foo := { foo : unit; bar : unit; }.

Definition foo_ := {|
  foo := tt;
  bar := tt;
|}.

End C.

Module D.

Record Foo := { foo : unit }.
Definition foo_ := {| foo := tt |}.

End D.

Module E.

Record Foo := { foo : unit; }.
Definition foo_ := {| foo := tt; |}.

End E.

Module F.

Record Foo := { foo : nat * nat -> nat -> nat }.

Definition foo_ := {| foo '(x,y) n := x+y+n |}.

End F.

Module RecordWith.

  Record R A := { x : nat; y : A; z := x; e : z = 0 }.

  Definition atunit : R (unit -> unit) :=
    {| x := 0; y (_:match tt with tt => unit end) := tt; e := eq_refl |}.

  Definition bli (a:R (R unit)) := {| a.(y _) with y := true |}.

  Fail Check fun (a:R (R unit)) => {| a.(y _) with y := true; z := _ |}.

  Fail Check {| atunit with x := 0; y := 0; e := eq_refl |}.

End RecordWith.
