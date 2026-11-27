
Set Universe Polymorphism.

Fail Cumulative Inductive token@{*u v | u < v} : Set :=
| make_token (ghost : Type@{v} := Type@{u}).

Cumulative Inductive token@{u v | u < v} : Set :=
| make_token (ghost : Type@{v} := Type@{u}).

Definition read_token@{u v | u < v} (t : token@{u v}) : Type@{v} :=
  match t with make_token ghost => ghost end.

Fail Definition small@{u v | Set < u, u < v} : Type@{u} :=
  read_token@{Set u} (make_token@{u v}).

(* Definition small_is_universe@{u v | Set < u, u < v} : *)
(*   @eq Type@{v} small@{u v} Type@{u} := eq_refl. *)

(* Require Import Hurkens. *)

(* Definition contradiction : False := *)
(*   TypeNeqSmallType.paradox small (eq_sym small_is_universe). *)

(* Print Assumptions contradiction. *)
