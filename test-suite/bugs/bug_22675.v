
Set Universe Polymorphism.

Cumulative Inductive token@{u v | u < v} : Set :=
| make_token (ghost : Type@{v} := Type@{u}).

Definition read_token@{u v | u < v} (t : token@{u v}) : Type@{v} :=
  match t with make_token ghost => ghost end.

Fail Cumulative Inductive outer@{*u v | u < v} : Set :=
| make_outer (x : token@{u v} := make_token@{u v}).

Fail Cumulative Inductive outer@{+u v | u < v} : Set :=
| make_outer (x : token@{u v} := make_token@{u v}).

Cumulative Inductive outer@{u v | u < v} : Set :=
| make_outer (x : token@{u v} := make_token@{u v}).

Definition read_outer@{u v | u < v} (o : outer@{u v}) : token@{u v} :=
  match o with make_outer x => x end.

Fail Definition small_outer@{u v | Set < u, u < v} : Type@{u} :=
  read_token@{Set u} (read_outer@{Set u} (make_outer@{u v})).

(* The type of the let-in may name another universe that the declaration's
   constraints force equal to the one the body uses. The type carries that
   universe too. *)
Cumulative Inductive eq_outer@{*u w v | u = w, u < v, w < v} : Set :=
| make_eq_outer (x : token@{w v} := make_token@{u v}).

Definition read_eq_outer@{u w v | u = w, u < v, w < v}
  (o : eq_outer@{u w v}) : token@{w v} :=
  match o with make_eq_outer x => x end.

Fail Definition small_eq@{u v | Set < u, u < v} : Type@{u} :=
  read_token@{Set u} (read_eq_outer@{Set Set u} (make_eq_outer@{u u v})).

(* The type is a CUMUL position, as the type of an argument is: a universe
   which occurs only there keeps the variance that type gives it, here
   covariant. *)
Fail Cumulative Inductive only_type@{*u} : Set :=
| make_only_type (x : Type@{u} := nat).

Cumulative Inductive only_type@{+u} : Set :=
| make_only_type (x : Type@{u} := nat).

(* A universe which is irrelevant for the inductive the body names stays
   irrelevant: no let-in of its constructors can read it back. This holds
   where the type reaches that inductive through a constant as well. *)
Cumulative Inductive phantom@{*u} : Set := make_phantom.

Cumulative Inductive holder@{*u} : Set :=
| make_holder (x : phantom@{u} := make_phantom@{u}).

Definition type_id@{w} (A : Type@{w}) : Type@{w} := A.

Cumulative Inductive aliased_holder@{*u} : Set :=
| make_aliased_holder (x : type_id@{u} (phantom@{u}) := make_phantom@{u}).

(* Definition small_outer_is_universe@{u v | Set < u, u < v} : *)
(*   @eq Type@{v} small_outer@{u v} Type@{u} := eq_refl. *)

(* From Stdlib Require Import Hurkens. *)

(* Definition contradiction : False := *)
(*   TypeNeqSmallType.paradox small_outer (eq_sym small_outer_is_universe). *)

(* Print Assumptions contradiction. *)
