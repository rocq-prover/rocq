Sort Extr.

Constraint Extr ~> SProp.
Constraint Type ~> Extr.

Set Universe Polymorphism.

Class LargeElimSort@{s t| l l' | t ~> Type , l < l'} : Type@{t|l'+1} :=
{ Univ : Type@{s|l'} ;
  code : Type@{s|l} -> Univ ;   
  El : Univ -> Type@{s|l} ;
  El_code A : El (code A) = A :> Type@{s|l} }.

Instance ExtrLargeElimSort@{l l'| l < l'} : LargeElimSort@{Extr Type | l l'}. 
Admitted. 

Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

Inductive unit : Type := tt.
Inductive empty : Type := .

Definition nat_rect@{i} := nat_poly@{Type Type | i}.
Definition nat_rec@{i} := nat_poly@{Type Type | i}.
Definition nat_ind@{i} := nat_poly@{Type Prop | i}.
Definition nat_sind@{i} := nat_poly@{Type SProp | i}.

Definition P@{s|u u'|u <u'} {H:LargeElimSort@{s Type|u u'}} (n : nat@{s|}) :=
  match n return H.(Univ) with
    O => code unit@{s|u}
  | _ => code empty@{s|u}
  end.

Lemma eq_true@{s|u u'|u <u'} {H:LargeElimSort@{s Type|u u'}} : forall (n:nat@{s|}), O = n -> H.(El) (P n).
Proof.
  intros b e. destruct e. cbn. eapply (eq_poly _ (fun X => X) tt _ (eq_sym@{Type s|_ _} (H.(El_code) unit))).
Qed.

Lemma nat_discr@{s|u u'|u <u'} {H:LargeElimSort@{s Type|u u'}} (n : nat@{s|}): O = S n -> empty@{s|u}.
Proof.
  intro e. pose proof (eq_true _ e). eapply (eq_poly _ (fun X => X) X _ (H.(El_code) _)).
Qed.

Lemma nat_discr_extr (n : nat@{Extr|}): O = S n -> False.
Proof.
  intro e. pose proof (nat_discr n e). destruct X.
Qed.  

Inductive Vect (A : Type) : nat@{Extr|} -> Type :=
| vnil : Vect A O
| vcons : forall (a:A) n, Vect A n -> Vect A (S n).

Fail Definition length A n : Vect A n -> nat@{Type|} := fun _ => n. 

Fixpoint length A n : Vect A n -> nat@{Type|} := 
  fun v => match v with 
    | vnil _ => O 
    | vcons _  a n v => S (length A n v)
    end.
