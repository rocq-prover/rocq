(* Rewriting with a rule whose evars have types mentioning universes that
   were defined (substituted) while the rule was interpreted. This is the
   shape of mathcomp's [size_pmap_sub] proof. *)
Require Import ssreflect ssrfun ssrbool.

Fixpoint count {T : Type} (a : pred T) (s : list T) : nat :=
  match s with nil => 0 | cons x s' => (if a x then 1 else 0) + count a s' end.

Lemma eq_count {T : Type} {a1 a2 : pred T} : a1 =1 a2 -> count a1 =1 count a2.
Proof. by move=> E; elim=> //= x s ->; rw E. Qed.

Structure subType {T : Type} (P : pred T) :=
  SubType { sub_sort :> Type; insub : T -> option sub_sort;
            isSome_insub_ax : (fun x => isSome (insub x)) =1 P }.

Lemma isSome_insub {T : Type} {P : pred T} (sT : subType P) :
  (fun x => isSome (@insub T P sT x)) =1 P.
Proof. exact: isSome_insub_ax. Qed.

Section S.
Variables (T : Type) (p : pred T) (sT : subType p).

Lemma count_insub s : count (fun x => isSome (@insub _ _ sT x)) s = count p s.
Proof. by rw (eq_count (isSome_insub _)). Qed.
End S.
