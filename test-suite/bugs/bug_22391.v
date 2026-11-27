Set Universe Polymorphism.

NonCumulative Inductive token@{u v | u < v} : Set :=
| make_token (ghost : Type@{v} := Type@{u}).

Definition read_token@{u v | u < v} (t : token@{u v}) : Type@{v} :=
  match t with make_token ghost => ghost end.

Definition read_constant@{lo hi top | lo < hi, hi < top}
    (t : token@{hi top}) : Type@{top} :=
  match t with make_token ghost => Type@{lo} end.

Definition collision@{lo hi top | lo < hi, hi < top}
    (t : token@{hi top}) :
  @eq Type@{top}
    (read_token@{hi top} t) (read_constant@{lo hi top} t).
Proof.
  exact_no_check (@eq_refl Type@{top} (read_token@{hi top} t)).
  Fail Defined.
Abort.

(* Definition collapse@{lo hi top | lo < hi, hi < top} : *)
(*   @eq Type@{top} Type@{hi} Type@{lo} := *)
(*   collision@{lo hi top} make_token@{hi top}. *)

(* Require Import Hurkens. *)

(* Definition contradiction : False := *)
(*   TypeNeqSmallType.paradox _ collapse. *)

(* Print Assumptions contradiction. *)
