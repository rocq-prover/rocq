Set Universe Polymorphism.
Set Definitional UIP.

Inductive seq@{i} {A : Type@{i}} (x : A) : A -> SProp :=
| srefl : seq x x.

Definition transport@{i j} {A : Type@{i}} (P : A -> Type@{j})
    {x y : A} (e : seq x y) : P x -> P y :=
  match e in seq _ y return P x -> P y with
  | srefl _ => fun v => v
  end.

(* incorrect irrelevant annotation *)
Fail Cumulative Inductive Hidden@{*u z w h | u < z, z < w, w < h}
    (Y : Type@{w}) (e : @seq@{h} Type@{w} Type@{z} Y)
    (Q : Y -> Type@{w}) : Type@{w} :=
| hide : Q (@transport@{h w} Type@{w} (fun T : Type@{w} => T)
              Type@{z} Y e Type@{u}) -> Hidden Y e Q.

Cumulative Inductive Hidden@{u z w h | u < z, z < w, w < h}
    (Y : Type@{w}) (e : @seq@{h} Type@{w} Type@{z} Y)
    (Q : Y -> Type@{w}) : Type@{w} :=
| hide : Q (@transport@{h w} Type@{w} (fun T : Type@{w} => T)
              Type@{z} Y e Type@{u}) -> Hidden Y e Q.

Definition Box@{u z w h | u < z, z < w, w < h} : Type@{w} :=
  Hidden@{u z w h} Type@{z}
    (@srefl@{h} Type@{w} Type@{z}) (fun A : Type@{z} => A).

Definition box@{u z w h | u < z, z < w, w < h}
    (A : Type@{u}) : Box@{u z w h} :=
  hide@{u z w h} Type@{z}
    (@srefl@{h} Type@{w} Type@{z}) (fun A : Type@{z} => A) A.

Definition unbox@{u z w h | u < z, z < w, w < h}
    (x : Box@{u z w h}) : Type@{u} :=
  match x with hide _ _ _ A => A end.

Fail Definition lower@{lo hi z w h | lo < hi, hi < z, z < w, w < h}
    (A : Type@{hi}) : Type@{lo} :=
  unbox@{lo z w h} (box@{hi z w h} A).

(* Definition small@{lo hi z w h | lo < hi, hi < z, z < w, w < h} *)
(*     : Type@{lo} := lower@{lo hi z w h} Type@{lo}. *)

(* Definition small_is_universe@{lo hi z w h + | lo < hi, hi < z, z < w, w < h +} *)
(*     : @eq Type@{hi} small@{lo hi z w h} Type@{lo} := eq_refl. *)

(* From Stdlib Require Import Hurkens. *)

(* Definition contradiction : False := *)
(*   TypeNeqSmallType.paradox small (eq_sym small_is_universe). *)

(* Print Assumptions contradiction. *)
(* (* seq needs UIP *) *)
