From Corelib Require Import Program.Tactics.
Generalizable All Variables.
#[local] Obligation Tactic := idtac.
Class Foo := { x : True }.
Class Bar (f : Foo) := { y : True }.
Program Instance foo : Foo := { }.
Fail Program Instance bar : Bar foo := { }.
Admit Obligations.
