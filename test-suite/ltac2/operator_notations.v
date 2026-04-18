Require Import Ltac2.Ltac2.

(* Associativity *)
Ltac2 Type a.
Ltac2 Type b.
Ltac2 Type rec c := { p : c }.
Ltac2 Type ('x,'y) h := { h : 'y -> 'x }.

(** Associativity *)

(* Sanity check: the term does not typecheck when wrongly associated. *)
Fail Ltac2 test_app_assoc_fail (f : b -> a) (g : c -> b) (c : c) :=
  (f @@ g) c.
Succeed Ltac2 test_app_assoc_1 (f : b -> a) (g : c -> b) (c : c) :=
  f @@ g c.
Succeed Ltac2 test_app_assoc_2 (f : b -> a) (g : c -> b) (c : c) :=
  f @@ (g c).
Succeed Ltac2 test_app_assoc_3 (f : b -> a) (g : c -> b) (c : c) :=
  f @@ g @@ c.
Succeed Ltac2 test_app_assoc_4 (f : b -> a) (g : c -> b) (c : c) :=
  f @@ (g @@ c).

(* Sanity check: the term does not typecheck when wrongly associated. *)
Fail Ltac2 test_pipe_assoc_fail (f : b -> a) (g : c -> b) (c : c) :=
  c |> (g |> f).
Succeed Ltac2 test_pipe_assoc_1 (f : b -> a) (g : c -> b) (c : c) :=
  c |> g |> f.
Succeed Ltac2 test_pipe_assoc_2 (f : b -> a) (g : c -> b) (c : c) :=
  (c |> g) |> f.

(** Precedence *)
(* Sanity check: the term does not typecheck when the notation level is wrong
   w.r.t. the level of projections. *)
Fail Ltac2 test_app_prec_fail (f : b -> a) (g : c -> b) (c : c) :=
  (f @@ g @@ c).(p).
Ltac2 test_app_prec_1 (f : b -> a) (g : c -> b) (c : c) :=
  f @@ g @@ c.(p).
Ltac2 test_app_prec_2 (f : (a,b) h) (g : c -> b) (c : c) :=
  f.(h) @@ g @@ c.
Ltac2 test_app_prec_3 (f : b -> a) (g : (b,c) h) (c : c) :=
  f @@ g.(h) @@ c.

Ltac2 test_app_prec_if (g : c -> b) (c : c) :=
  if true then g @@ c else g @@ c.

(* Sanity check: the term does not typecheck when the notation level is wrong
   w.r.t. the level of projections. *)
Fail Ltac2 test_pip_prec_fail (f : (a,b) h) (g : c -> b) (c : c) :=
  (c |> g |> f).(h).
Ltac2 test_pip_prec_1 (f : (a,b) h) (g : c -> b) (c : c) :=
  c |> g |> f.(h).
Ltac2 test_pipe_prec_2 (f : b -> a) (g : (b,c) h) (c : c) :=
  c |> g.(h) |> f.
Ltac2 test_pipe_prec_3 (f : (a,b) h) (g : (b,c) h) (c : c) :=
  c |> g.(h) |> f.(h).
Ltac2 test_pipe_prec_4 (f : (a,b) h) (g : (b,c) h) (c : c) :=
  c.(p) |> g.(h) |> f.(h).

Ltac2 test_pipe_prec_if (g : c -> b) (c : c) :=
  if true then c |> g else c |> g.

Ltac2 test_app_pipe_2 (f : b -> a) (g : c -> b) (c : c) :=
  g @@ c |> f.

Fail Ltac2 test_app_pipe_fail (f : b -> a) (g : c -> b) (c : c) :=
  f @@ c |> g.

Ltac2 test_pipe_app_1 (t : b -> c -> a) (b : b) (c : c) :=
  c |> t @@ b.
