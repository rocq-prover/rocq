Set Universe Polymorphism.
Inductive sum@{s;u v|} (A : Univ@{s;u}) (B : Univ@{s;v}) : Univ@{s;max(u,v)} :=
  | inl : A -> sum A B
  | inr : B -> sum A B.
Arguments inl {A B}.
Arguments inr {A B}.

Fail Check (fun p : sum@{Prop;_ _} True False => match p return Set with inl a => unit | inr b => bool end).
(*
Error: The quality constraints are inconsistent: cannot enforce Prop -> Type because it would identify Type and Prop which is inconsistent.
This is introduced by the constraints Prop -> Type
*)


Inductive sBox@{s s';u|} (A:Univ@{s;u}) : Univ@{s';u} := sbox (_:A).

Fail Definition elim@{s s';u|} (A:Univ@{s;u}) (x:sBox@{s s';u} A) : A :=
  match x with sbox _ v => v end.
(* Error: Elimination constraints are not implied by the ones declared: s' -> s *)

Inductive sP : SProp := sC.

Fail Check match sC with sC => I end.
(*
Error: The quality constraints are inconsistent: cannot enforce SProp -> Prop because it would identify Prop and SProp which is inconsistent.
This is introduced by the constraints SProp -> Prop
*)
