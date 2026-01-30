Require Import Program.Wf.

Fail Program Fixpoint f n {measure n} := g n with g n {measure n} := f n.
