Require Import List Arith Max Omega Bool Setoid Wf_nat.

Hint Extern 1 (?f _ = ?f _) => f_equal.
Hint Extern 1 (?f _ _ = ?f _ _) => f_equal.
Hint Extern 1 (?f _ _ _ = ?f _ _ _) => f_equal.

(** Pour l'instant, on utilise le tiers exclu a un endroit *)
Require Import Classical.


(** * Les termes *)

(** Encore plus mini que mini-ML : un lambda-calcul, toujours sans types *)
(** On laisse juste une constante TDummy, ca ne coute rien *)

Inductive term : Set :=
  | TDummy : term
  | TVar : nat -> term
  | TFun : term -> term
  | TApply : term -> term -> term
.

Notation "a @ b" := (TApply a b) (at level 40).

(** Les valeurs possibles apres evaluation : constantes ou clotures *)

Inductive value : Set:=
  | VDummy : value 
  | VClos : list value -> term -> value
.


(** Variables libres *)

(** Est-ce que n est libre dans t ? *)

Fixpoint freevar (n:nat)(t:term) { struct t } : bool := 
 match t with 
    | TDummy => false
    | TVar k => if eq_nat_dec k n then true else false
    | TFun t => freevar (S n) t
    | t1@t2 => (freevar n t1) || (freevar n t2)
 end.

(** Termes clos *)

Definition clos t := forall n, freevar n t = false.
Definition clos_list l := forall t, In t l -> clos t.

(** termes clos au dela d'un certain indice *)

Definition clos_after n t := forall m, n<=m -> freevar m t = false. 

(** Substitution de n par u dans t (pour un u forcement clos).
    Les indices au dela de n dans t sont decrementes de 1. *)

Fixpoint subst n u t {struct t} :=
  match t with
    | TDummy => TDummy
    | TVar k => 
        match lt_eq_lt_dec k n with
          | inleft (left _) => TVar k
          | inleft (right _) => u
          | inright _ => TVar (pred k)
        end
    | TFun t => TFun (subst (S n) u t)
    | t1@t2 => (subst n u t1)@(subst n u t2)
  end
.

Notation "t [ n := u ]" := (subst n u t) 
 (at level 20, n at next level, left associativity).

(** Substitution par paquet: 
    Si l = [u0;u1;...], on remplace n par u0, n+1 par u1, etc. 
    Les indices au dela de n+(length l) sont decrementes de (length l). *)

Fixpoint subst_list n l t {struct t} := match t with 
   | TDummy => TDummy 
   | TVar k => if (le_lt_dec n k) then nth (k-n) l (TVar (k-length l))
               else TVar k
   | TFun t => TFun (subst_list (S n) l t)
   | t1@t2 => (subst_list n l t1)@(subst_list n l t2)
  end
.

Notation "t [ n ::= l ]" := (subst_list n l t) 
 (at level 20, n at next level, left associativity).


(** Une presentation alternative de la substitution par paquet, 
    par iteration de subst *)

Fixpoint subst_list_iter n l t {struct l} := match l with
   | nil => t
   | u::l => subst_list_iter n l (t[n:=u])
  end
.

Notation "t [ n ;;= l ]" := (subst_list_iter n l t) 
 (at level 20, n at next level, left associativity).

(** Une definition alternative de la cloture *) 

Definition closbis t := forall n u, t[n:=u] = t.




(** Resultats concernant termes, cloture et substitutions. *)

Lemma term_dec : forall t u : term, { t = u } + { t<>u }.
Proof.
decide equality.
apply eq_nat_dec.
Qed.

Lemma clos_after_App1 : 
 forall n t1 t2, clos_after n (t1@t2) -> clos_after n t1.
Proof.
 unfold clos_after; simpl; intros.
 destruct (orb_false_elim _ _ (H _ H0)); auto.
Qed.

Lemma clos_after_App2 : 
 forall n t1 t2, clos_after n (t1@t2) -> clos_after n t2.
Proof.
 unfold clos_after; simpl; intros.
 destruct (orb_false_elim _ _ (H _ H0)); auto.
Qed.

Lemma clos_after_Fun : 
 forall n t, clos_after n (TFun t) -> clos_after (S n) t.
Proof.
 unfold clos_after; simpl; intros.
 assert (n <= m-1) by omega.
 replace m with (S (m-1)) by omega; auto.
Qed.

Lemma clos_list_cons : forall a l, clos_list (a::l) <-> clos a /\ clos_list l.
Proof.
 split.
 split.
 intros; apply (H a); simpl; auto.
 intros u Hu; apply (H u); simpl; auto.
 destruct 1; intros u Hu; simpl in Hu; destruct Hu; subst; auto.
Qed.

Lemma clos_list_app : forall l l', 
 clos_list (l++l') <-> clos_list l /\ clos_list l'.
Proof.
 induction l; simpl; auto.
 intuition.
 intros u Hu; inversion Hu.
 intros; do 2 rewrite clos_list_cons; rewrite IHl; intuition.
Qed.

Ltac dec := 
  let H := fresh "H" in 
  destruct lt_eq_lt_dec as [[H|H]|H] ||
  destruct le_lt_dec as [H|H] || 
  destruct eq_nat_dec as [H|H] || idtac; 
  simpl; 
  trivial; 
  try (intros; discriminate); 
  try (elimtype False; omega);
  match goal with 
    | H:?n=?n  |- _ => clear H
    | H:?n<=?n |- _ => clear H
    | _ => idtac
  end.

Ltac orb H :=  destruct (orb_false_elim _ _ H); auto.

Ltac inv_clear H := inversion H; try clear H; subst.

(*
Ltac name_of te := 
 match goal with 
  | H : te |- _ => H
 end.
Tactic Notation "elim_on" constr(t):= let H:=name_of t in elim H.
*)

Lemma subst_clos_after : forall t n, 
   clos_after n t <-> (forall n0 t0, n <= n0 -> subst n0 t0 t = t).
Proof.
 induction t; unfold clos_after in *; simpl; intros.
 (* Dummy *)
 intuition.
 (* Var *)
 intuition; dec; subst.
 generalize (H _ H0); dec.
 assert (H' : n0 <= n) by omega; generalize (H _ H'); dec.
 generalize (H _ TDummy H0); dec.
 (* Fun *)
 destruct (IHt (S n)) as [IHa IHb]; clear IHt.
 split; intros.
 f_equal; apply IHa; auto with arith; intros.
 destruct m; auto with arith.
 inversion H1.
 apply IHb; auto with arith; intros.
 destruct n0; auto with arith.
 inversion H1.
 assert (H' : n <= n0) by omega; generalize (H _ t0 H'); congruence.
 (* Apply *)
 destruct (IHt1 n) as [IH1a IH1b]; clear IHt1.
 destruct (IHt2 n) as [IH2a IH2b]; clear IHt2.
 split; intros.
 f_equal; [apply IH1a | apply IH2a]; auto with arith; intros.
 orb (H _ H1).
 orb (H _ H1).
 rewrite IH1b; auto with arith; intros.
 rewrite IH2b; auto with arith; intros.
 generalize (H _ t0 H1); congruence.
 generalize (H _ t0 H1); congruence.
Qed.

Lemma clos_closbis : forall t, clos t <-> closbis t.
Proof.
 unfold clos, closbis; intros.
 destruct (subst_clos_after t 0); unfold clos_after in *.
 split; auto with arith.
Qed.

(** La consequence utile de tout ca: *)

Lemma subst_clos : forall t, clos t -> forall n u, t[n:=u] = t.
Proof.
 intros t H n u; rewrite clos_closbis in H; rewrite H; auto.
Qed.
Hint Resolve subst_clos.
Hint Extern 1 (?t=?t[_:=_]) => (symmetry; auto).

Lemma subst_list_clos : forall l t n, clos t -> t[n;;=l] = t.
Proof.
induction l; simpl; auto; intros.
rewrite (subst_clos _ H); auto.
Qed.
Hint Resolve subst_list_clos.
Hint Extern 1 (?t=?t[_;;=_]) => (symmetry; auto).

Lemma subst_freevar : forall t n u m, n <= m -> 
  clos u -> clos_after (S m) t -> clos_after m (t[n:=u]).
Proof.
unfold clos_after; induction t; simpl; auto; intros.
assert (~ S m <= n).
 intro H'; generalize (H1 _ H'); dec.
clear H1; do 3 dec.
apply IHt with (S m); auto with arith.
intros m1 Hm1.
replace m1 with (S (pred m1)) by omega; auto with arith.
apply orb_false_intro.
apply IHt1 with m; auto with arith.
intros m1 Hm1; orb (H1 _ Hm1).
apply IHt2 with m; auto with arith.
intros m1 Hm1; orb (H1 _ Hm1).
Qed.

Lemma subst_list_iter_freevar : forall l n t, 
  clos_list l -> 
  clos_after (n+length l) t -> 
  clos_after n (t[n;;=l]).
Proof.
induction l; simpl; auto; intros.
replace n with (n+0); auto with arith.
rewrite clos_list_cons in H; destruct H.
apply IHl; auto.
apply subst_freevar; auto with arith.
rewrite <- plus_n_Sm in H0; auto.
Qed.

Lemma subst_list_equiv : forall t l n, 
 clos_list l -> t[n;;=l] = t[n::=l].
Proof.
intros t l; revert t; induction l; simpl; auto; intros.
(* nil *)
clear H.
revert n; induction t; simpl; auto.
intro k; dec; destruct (n-k); auto with arith.
(* cons *)
rewrite clos_list_cons in H; destruct H.
assert (IH:=fun t n => IHl t n H0); clear IHl H0.
revert n; induction t; intros; rewrite IH; simpl; auto.
(* - var *)
rename n into k; rename n0 into n.
dec; dec.
 subst k; replace (n-n) with 0 by omega; simpl.
 rewrite <- IH; auto.
 replace (k-n) with (S (pred k - n)) by omega; simpl; dec.
 f_equal; f_equal; omega.
(* - fun *)
rewrite <- IHt; auto.
(* - app *)
rewrite <- IHt1; rewrite <- IHt2; auto.
Qed.

Lemma subst_commut : forall u u', clos u -> clos u' -> 
 forall t n n', n<=n' -> t[S n':=u'][n:=u] = t[n:=u][n':=u'].
Proof.
induction t; simpl; intros; auto with arith.
do 4 dec; auto.
Qed.
Hint Resolve subst_commut.

Lemma subst_list_iter_commut : forall l t u n, 
 clos u -> clos_list l -> 
 t[S n;;=l][n:=u] = t[n:=u][n;;=l].
Proof.
induction l; simpl; auto; intros.
rewrite clos_list_cons in H0; destruct H0.
rewrite IHl; auto.
Qed.
Hint Resolve subst_list_iter_commut.







(** * I) Semantique big-step avec environnement : *)

(**  Le predicat d'evaluation d'un terme dans un environnement (liste de valeurs) *)

Reserved Notation "e |= t --> v" (at level 100, t at next level).

Inductive BigStep : list value -> term -> value -> Prop:=
  | BigStep_Dum : forall e,  e |= TDummy --> VDummy
  | BigStep_Var : forall n e v, nth_error e n = Some v -> (e|=TVar n --> v)
  | BigStep_Fun : forall e t, e |= TFun t --> VClos e t
  | BigStep_App : forall e e' t t1 t2 v v2,
     (e|=t1-->VClos e' t) -> 
     (e|=t2-->v2) -> 
     (v2::e'|=t-->v) -> 
     (e|=t1@t2-->v)
where "e |= t --> v" := (BigStep e t v).

Hint Constructors BigStep.

(** En cas de succes dans l'evaluation, une seule arrivee possible *)

Lemma BigStep_det : forall e t v, (e|=t-->v) -> forall v', (e|=t-->v') -> v = v'.
Proof.
 induction 1; inversion_clear 1; auto; try congruence.
 assert (A : VClos e' t = VClos e'0 t0) by auto.
 inv_clear A.
 assert (A : v2 = v1) by auto.
 subst v2; auto.
Qed.




(** Termes avec environnement inclus *)

Inductive eterm : Set := 
 | EDummy : eterm 
 | EVar : nat -> eterm 
 | EFun : list value -> term -> eterm 
 | EApply : eterm -> eterm -> eterm.

Notation "t @: u" := (EApply t u) (at level 40).

Fixpoint v2et v := match v with 
 | VDummy => EDummy
 | VClos e t => EFun e t
end.

Lemma v2et_inj: forall v v', v2et v = v2et v' -> v = v'.
Proof.
destruct v; destruct v'; simpl; intros; try discriminate; congruence.
Qed.
Hint Resolve v2et_inj.

Lemma v2et_inj_list: forall vl vl', map v2et vl = map v2et vl' -> vl = vl'.
Proof.
induction vl; destruct vl'; simpl; intros; try discriminate; try congruence.
inv_clear H; auto.
Qed.


Fixpoint t2et e t { struct t } := match t with 
 | TDummy => EDummy
 | TVar n => match nth_error e n with 
    | None => EVar (n-length e)
    | Some v => v2et v
   end
 | TFun t => EFun e t
 | t@u => (t2et e t)@:(t2et e u)
end.

Fixpoint v2t v := match v with
 | VDummy => TDummy
 | VClos e f => TFun (subst_list_iter 1 (map v2t e) f)
end.

Fixpoint et2t t := match t with 
 | EDummy => TDummy
 | EVar n => TVar n
 | EFun e t => TFun (subst_list_iter 1 (map v2t e) t)
 | t@:u => (et2t t)@(et2t u) 
end.

Lemma et2t_v2et : forall v, 
 et2t (v2et v) = v2t v.
Proof.
 induction v; simpl; auto.
Qed.




(** II) Semantique small-step avec environnements dans les termes *)

Reserved Notation "u --:> v" (at level 100).
Reserved Notation "u ==:> v" (at level 100).

Inductive ESmallStep : eterm -> eterm -> Prop := 
  | ESmallStep_beta : forall e t u v, u = v2et v -> 
     ((EFun e t)@:u --:> t2et (v::e) t)
  | ESmallStep_app1 : forall u v t, (u--:>v) -> (u@:t --:> v@:t)
  | ESmallStep_app2 : forall u v t, (u--:>v) -> (t@:u --:> t@:v)
where "u --:> v" := (ESmallStep u v).

Hint Constructors ESmallStep.

Inductive ESmallSteps : eterm -> eterm -> Prop :=
  | ESmallSteps_refl : forall t, (t==:>t)
  | ESmallSteps_trans : forall t u r, (t--:>u) -> (u==:>r) -> (t==:>r)
where "u ==:> v" := (ESmallSteps u v).

Hint Constructors ESmallSteps.

Fixpoint ESmallStepN n := match n with 
  | O => fun t r => t=r
  | S n => fun t r => exists s, (t--:>s) /\ ESmallStepN n s r
 end.
Notation "t ==[ n ]:> u" := (ESmallStepN n t u) (at level 100, n at next level).

Definition ESmallSteps' t u := exists n, ESmallStepN n t u.
Notation "t ==[]:> u" := (ESmallSteps' t u) (at level 100, n at next level).

Lemma ESmallSteps_alt : forall t u, (t==:>u) <-> (t==[]:>u).
Proof.
 split.
 induction 1.
 exists 0; simpl; auto.
 destruct IHESmallSteps as (n,H1).
 exists (S n); simpl; exists u; auto.
 destruct 1 as (n,H).
 revert t u H.
 induction n; simpl.
 intros; rewrite H; auto.
 destruct 1 as (s,(H1,H2)); eauto.
Qed.


Lemma ESmallStep_v2et : forall t u, (t--:>u) -> forall v, t = v2et v -> 
 u = v2et v.
Proof.
 induction 1; simpl; auto; intros; try (destruct v0; discriminate; fail).
Qed.

Lemma ESmallSteps_v2et : forall t u, (t==:>u) -> forall v, t = v2et v -> 
 u = v2et v.
Proof.
 induction 1; auto.
 intros.
 apply IHESmallSteps.
 eapply ESmallStep_v2et; eauto.
Qed.

Lemma ESmallSteps_trans2 : forall t u r,
  (t==:>u) -> (u==:>r) -> (t==:>r).
Proof.
  induction 1; intros; auto.
  eapply ESmallSteps_trans; eauto.
Qed.

Lemma ESmallStep_is_ESmallSteps : forall t u, (t--:>u) -> (t==:>u).
Proof.
  eauto.
Qed.

Lemma ESmallSteps_app1 : 
 forall t u r, (t==:>u) -> (t@:r ==:> u@:r).
Proof.
 induction 1; auto.
 eapply ESmallSteps_trans; eauto.
Qed.

Lemma ESmallSteps_app2 : 
 forall t u r, (t==:>u) -> (r@:t ==:> r@:u).
Proof.
 induction 1; auto.
 eapply ESmallSteps_trans; eauto.
Qed.

(**  I) -> II) *)

Lemma BigStep_ESmallSteps : forall e t v, 
  (e|=t-->v) -> (t2et e t ==:> v2et v).
Proof.
 induction 1; simpl; auto; intros.
 rewrite H; simpl; auto.
 eapply ESmallSteps_trans2.
 eapply ESmallSteps_app1; eauto.
 eapply ESmallSteps_trans2.
 eapply ESmallSteps_app2; eauto.
 eapply ESmallSteps_trans2; [ |eassumption].
 apply ESmallStep_is_ESmallSteps; simpl; auto.
Qed.





Lemma BigStep_v2et_t2et : forall v e t, v2et v = t2et e t -> (e|=t-->v).
Proof.
 induction v; simpl; auto; intros.

 destruct t; simpl in *; try discriminate; auto.
 constructor.
 destruct (nth_error e n); try discriminate.
 destruct v; try discriminate; auto.

 destruct t0; simpl in *; try discriminate; auto.
 constructor.
 destruct (nth_error e n); try discriminate.
 destruct v; simpl in *; try discriminate; inversion H; auto.
 inversion H; auto.
Qed.

Lemma ESmallStepN_inv_app : forall n t u v, 
(t@:u ==[n]:> v2et v) -> 
exists e, exists t', exists v', exists n1, exists n2, exists n3, 
  S (n1+n2+n3) = n /\ 
  (u ==[n1]:> v2et v') /\
  (t ==[n2]:> EFun e t')  /\
  (t2et (v'::e) t' ==[n3]:> v2et v).
Proof.
induction n; simpl; intros.
destruct v; discriminate.
destruct H as (s,(Hs1,Hs2)).
inv_clear Hs1.

exists e; exists t0; exists v0; exists 0; exists 0; exists n.
repeat split; simpl; auto.

rename v0 into t'.
destruct (IHn _ _ _ Hs2) as (e1,(t1,(v1,(n1,(n2,(n3,(H,(H0,H1)))))))); clear IHn.
exists e1; exists t1; exists v1; exists n1; exists (S n2); exists n3.
repeat split; simpl; auto; destruct H1; auto.
omega.
exists t'; auto.

rename v0 into u'.
destruct (IHn _ _ _ Hs2) as (e1,(t1,(v1,(n1,(n2,(n3,(H,(H0,H1)))))))); clear IHn.
exists e1; exists t1; exists v1; exists (S n1); exists n2; exists n3.
repeat split; simpl; auto; destruct H1; auto.
exists u'; auto.
Qed.


Lemma ESmallStepN_BigStep : forall n t e v, 
  (t2et e t ==[n]:> v2et v) -> (e|=t-->v).
Proof.
 induction n using lt_wf_ind.
 induction t; simpl; auto; intros.

 destruct n; simpl in *.
 destruct v; try discriminate; auto.
 destruct H0 as (x,(Hx,Hx')).
 inversion Hx.

 constructor.
 destruct (nth_error e n0).
 f_equal.
 apply v2et_inj.
 symmetry.
 apply (ESmallSteps_v2et (v2et v0) (v2et v)); auto.
 rewrite ESmallSteps_alt.
 exists n; auto.
 destruct n; simpl in *.
 destruct v; discriminate.
 destruct H0 as (x,(Hx,Hx')).
 inversion Hx.

 destruct n; simpl in *; auto.
 destruct v; simpl in *; try discriminate.
 inversion H0; constructor; auto.
 destruct H0 as (x,(Hx,Hx')).
 inversion Hx.

 destruct (ESmallStepN_inv_app _ _ _ _ H0) as (e',(t',(v',(n1,(n2,(n3,H3)))))).
 intuition.
 apply BigStep_App with e' t' v'.
 eapply (H n2); eauto; omega.
 eapply (H n1); eauto; omega.
 eapply (H n3); eauto; omega.
Qed.

(** II) -> I) *)

Lemma ESmallSteps_BigStep : forall e t v, 
  (t2et e t ==:> v2et v) -> (e|=t-->v).
Proof.
intros.
rewrite ESmallSteps_alt in H.
destruct H as (n,H).
eapply ESmallStepN_BigStep; eauto.
Qed.





(** III) Semantique small-step completement sans environnement *)

Inductive IsValue : term -> Prop := 
  | IsValue_Dummy : IsValue TDummy 
  | IsValue_Fun : forall t, IsValue (TFun t).

Hint Constructors IsValue.

Reserved Notation "u --> v" (at level 100).
Reserved Notation "u ==> v" (at level 100).

Inductive SmallStep : term -> term -> Prop :=
  | SmallStep_beta : forall t1 t2, IsValue t2 -> 
    ((TFun t1)@t2 --> t1[0:=t2])
  | SmallStep_app1 : forall u v t, (u-->v) -> (u@t-->v@t)
  | SmallStep_app2 : forall u v t, (u-->v) -> (t@u-->t@v)
where "t --> u" := (SmallStep t u).

Hint Constructors SmallStep.

Inductive SmallSteps : term -> term -> Prop :=
  | SmallSteps_refl : forall t, (t==>t)
  | SmallSteps_trans : forall t u r, (t-->u) -> (u==>r) -> (t==>r)
where "t ==> u" := (SmallSteps t u).

Hint Constructors SmallSteps.

Fixpoint SmallStepN n := match n with 
  | O => fun t r => t=r
  | S n => fun t r => exists s, (t-->s) /\ SmallStepN n s r
 end.
Notation " t ==[ n ]> u " := (SmallStepN n t u) (at level 100, n at next level).

Definition SmallSteps' t u := exists n, SmallStepN n t u.
Notation " t ==[]> u" := (SmallSteps' t u) (at level 100, n at next level).

Lemma SmallSteps_alt : forall t u, (t==>u) <-> (t==[]>u).
Proof.
 split.
 induction 1.
 exists 0; simpl; auto.
 destruct IHSmallSteps as (n,H1).
 exists (S n); simpl; exists u; auto.
 destruct 1 as (n,H).
 revert t u H.
 induction n; simpl.
 intros; rewrite H; auto.
 destruct 1 as (s,(H1,H2)); eauto.
Qed.





Lemma SmallSteps_trans2 : forall t u r,
  (t==>u) -> (u==>r) -> (t==>r).
Proof.
  induction 1; intros; auto.
  eapply SmallSteps_trans; eauto.
Qed.

Lemma SmallStep_is_SmallSteps : forall t u,
  (t-->u) -> (t==>u).
Proof.
  eauto.
Qed.

Lemma SmallSteps_app1 : forall t u r, (t==>u) -> (t@r==>u@r).
Proof.
 induction 1; auto.
 eapply SmallSteps_trans; eauto.
Qed.

Lemma SmallSteps_app2 : forall t u r, (t==>u) -> (r@t==>r@u).
Proof.
 induction 1; auto.
 eapply SmallSteps_trans; eauto.
Qed.

Lemma IsValue_v2t : forall v, IsValue (v2t v).
Proof.
 induction v; simpl; auto.
Qed.
Hint Resolve IsValue_v2t.

Inductive val_clos : value -> Prop := 
 | clos_VDummy : val_clos VDummy
 | clos_Vclos : forall e t, env_clos e -> 
                            clos_after (S (length e)) t ->
                            val_clos (VClos e t)
with env_clos : list value -> Prop := 
 | clos_nil : env_clos nil 
 | clos_cons : forall v e, val_clos v -> env_clos e -> env_clos (v::e).

Hint Constructors val_clos env_clos.

Scheme val_clos_ind2 := Minimality for val_clos Sort Prop 
with env_clos_ind2 := Minimality for env_clos Sort Prop.

Lemma env_clos_app : 
 forall e1 e2, env_clos e1 -> env_clos e2 -> env_clos (e1++e2).
Proof.
 induction e1; simpl; auto.
 inversion_clear 1; intros.
 constructor; auto.
Qed.

Lemma v2t_clos : forall v, val_clos v -> clos (v2t v). (* RECIPROQUE FAUSSE ! *)
Proof.
 apply (val_clos_ind2 
         (fun v => clos (v2t v)) 
         (fun e => forall t, In t (map v2t e) -> clos t)); 
 simpl; auto; intros.
 
 red; simpl; auto.

 red; intros; simpl.
 apply subst_list_iter_freevar; auto with arith.
 red; intros.
 apply H1.
 rewrite map_length in H2; omega.

 contradiction.
 
 intuition.
 subst t; auto.
Qed.

Hint Resolve v2t_clos.

Lemma env_ok: forall e, env_clos e -> clos_list (map v2t e). (* RECIPROQUE FAUSSE *)
Proof.
induction e; unfold clos_list in *; simpl; auto.
contradiction.
inversion_clear 1.
destruct 1; auto.
subst t; apply v2t_clos; auto.
Qed.

Hint Resolve env_ok.

Definition do_env_subst e := subst_list 0 (map v2t e).  

Lemma do_env_subst_clos : 
 forall e t, env_clos e -> clos t -> do_env_subst e t = t. 
Proof.
intros.
unfold do_env_subst.
rewrite <- subst_list_equiv.
apply subst_list_clos; auto.
apply env_ok; auto.
Qed.

Definition normal t := forall u, ~(t-->u).

Lemma et2t_t2et : 
 forall t e, env_clos e -> et2t (t2et e t) = do_env_subst e t.
Proof.
 induction t; unfold do_env_subst in *; simpl; auto; intros.
 
 replace (n-0) with n by omega.
 revert n; induction e; destruct n; simpl; auto.
 apply et2t_v2et.
 inv_clear H; auto.
 
 f_equal; auto; rewrite subst_list_equiv; auto.
Qed.

Inductive eclos : eterm -> Prop := 
 | eclos_EDummy : eclos EDummy
 | eclos_EFun : 
    forall e t, env_clos e -> clos_after (S (length e)) t -> eclos (EFun e t)
 | eclos_EApply : 
    forall t u, eclos t -> eclos u -> eclos (EApply t u).

Hint Constructors eclos.

Lemma eclos_clos_val_1 : forall v, eclos (v2et v) -> val_clos v.
Proof.
 destruct v; simpl in *; auto; intros.
 inversion H; auto.
Qed.

Lemma eclos_clos_val_2 : forall v, val_clos v -> eclos (v2et v).
Proof.
 destruct v; simpl in *; auto; intros.
 inversion H; auto.
Qed.

Hint Resolve eclos_clos_val_1 eclos_clos_val_2.

Lemma ESmallStep_SmallStep : forall t u, eclos t -> 
 (t--:>u) -> (et2t t --> et2t u).
Proof.
 induction 2; simpl; intros; auto.
 subst u.
 inversion_clear H.
 inversion_clear H0.
 rewrite et2t_t2et.
 rewrite et2t_v2et.
 unfold do_env_subst.
 rewrite <- subst_list_equiv; simpl.
 rewrite <- subst_list_iter_commut; auto.

 red; intros.
 simpl in H0; destruct H0.
 subst t0; auto.
 revert t0 H0; change (clos_list (map v2t e)).
 apply env_ok; auto.
 constructor; auto.

 inv_clear H; auto.

 inv_clear H; auto.
Qed.

Lemma eclos_t2et : forall t e, env_clos e -> clos_after (length e) t -> 
 eclos (t2et e t).
Proof.
 induction t; simpl; intros.
 constructor.
 red in H0; simpl in H0.
 assert (~(length e <= n)).
  generalize (H0 n).
  destruct (eq_nat_dec n n).
  intros; intro.
  assert (H3:= H1 H2); discriminate.
  elim n0; auto.
 assert (n<length e) by omega.
 clear H0 H1.
 revert n H H2; clear; induction e; simpl; intros.
 inversion H2.
 inversion_clear H.
 destruct n; simpl; auto with arith.

 constructor; auto.
 apply clos_after_Fun; auto.

 constructor; auto.
 apply IHt1; auto.
 eapply clos_after_App1; eauto.
 apply IHt2; auto.
 eapply clos_after_App2; eauto.
Qed.

Lemma ESmallStep_eclos : forall t u, (t--:>u) -> eclos t -> eclos u.
Proof.
 induction 1; simpl; intros; auto.
 inversion_clear H0.
 inversion_clear H1.

 subst u; apply eclos_t2et; auto.

 inversion_clear H0; auto.
 inversion_clear H0; auto.
Qed.

(* II) -> III) *)

Lemma ESmallSteps_SmallSteps : forall t u, eclos t -> 
 (t==:>u) -> (et2t t ==> et2t u).
Proof.
induction 2; auto; intros.
econstructor.
eapply ESmallStep_SmallStep; eauto.
apply IHESmallSteps.
eapply ESmallStep_eclos; eauto.
Qed.





(* Ce CBV est _tres_ confluent, heureusement, vu que 
   l'ordre des calculs est quasi deterministe  *)

Lemma SmallStep_Church_Rosser: forall a b c, b<>c -> 
 (a-->b) -> (a-->c) -> exists d, (b-->d) /\ (c-->d).
Proof.
induction a; intros.
inversion H0.
inversion H0.
inversion H0.
inversion H0; inversion H1; clear H0 H1; subst.

inversion H6; clear H6; subst.
elim H; auto.

inversion H9.

elimtype False.
revert H5 H9; clear; induction 1; inversion 1.

inversion H5.

destruct (IHa1 v v0) as (d,(Hd1,Hd2)); auto.
exists (d@a2); auto.

exists (v@v0); auto.

elimtype False.
revert H5 H9; clear; induction 1; inversion 1.

exists (v0@v); auto.

destruct (IHa2 v v0) as (d,(Hd1,Hd2)); auto.
exists (a1@d); auto.
Qed.
Lemma SmallStepN_unique_nf : forall n a b c, normal b -> 
 (a==[n]>b) -> (a-->c) -> exists p, (c==[p]>b) /\ p < n.
Proof.
induction n; intros.
simpl in H0; subst b.
elim (H _ H1).
simpl in H0; destruct H0 as (d,(Hd1,Hd2)).
destruct (term_dec c d).
subst d.
exists n; auto with arith.
destruct (SmallStep_Church_Rosser _ _ _ n0 H1 Hd1) as (e,(He1,He2)); auto.
destruct (IHn _ _ _ H Hd2 He2) as (p,(Hp1,Hp2)).
exists (S p); split; auto with arith.
exists e; auto.
Qed.

Lemma SmallStep_not_enormal : forall t u, 
 (et2t t --> u) -> exists u', (t--:>u').
Proof.
intros; remember (et2t t) as r; revert t Heqr. 
induction H; simpl; intros; auto.

destruct t; simpl in Heqr; try discriminate; inv_clear Heqr.
destruct t3; simpl in H1; try discriminate; inv_clear H1.
assert (exists v, v2et v = t4).
 revert H; clear.
 destruct t4; simpl; try (inversion 1; fail).
 intros; exists VDummy; auto.
 intros; exists (VClos l t); auto.
destruct H0 as (v, Hv).
eauto.

rename t into r; rename t0 into t.
destruct t; simpl in Heqr; try discriminate; inv_clear Heqr.
destruct (IHSmallStep t1) as (u,Hu); auto.
exists (u@:t2); auto.

rename t into r; rename t0 into t.
destruct t; simpl in Heqr; try discriminate; inv_clear Heqr.
destruct (IHSmallStep t2) as (u,Hu); auto.
exists (t1@:u); auto.
Qed.


Lemma SmallStepN_ESmallSteps : forall n t u, eclos t -> normal u -> 
 (et2t t ==[n]> u) -> exists u', (t==:>u') /\ et2t u' = u.
Proof.
induction n using lt_wf_ind; intros.
(* Ici, on raisonne de manière classique *)
assert ((exists u, (t--:>u)) \/ (forall u, ~(t--:>u))).
 destruct (classic (exists u, (t--:>u))); auto.
 right; apply not_ex_all_not; auto.
destruct H3.
destruct H3 as (t', Ht').
assert (H4:=ESmallStep_SmallStep _ _ H0 Ht').
destruct (SmallStepN_unique_nf _ _ _ _ H1 H2 H4) as (p,(Hp1,Hp2)).
assert (H5:=ESmallStep_eclos _ _ Ht' H0).
destruct (H _ Hp2 _ _ H5 H1 Hp1) as (u',(Hu1,Hu2)).
exists u'; split; auto.
econstructor; eauto.

destruct n.
simpl in *; subst u.
exists t; auto.
simpl in H0; destruct H2 as (u0,(Hu1,Hu2)).
destruct (SmallStep_not_enormal _ _ Hu1); auto.
elim (H3 _ H2).
Qed.

(** III) -> II) *)

Lemma SmallSteps_ESmallSteps : forall t u, clos t -> normal u -> 
 (t==>u) -> exists u', (t2et nil t ==:> u') /\ et2t u' = u.
Proof.
intros.
rewrite SmallSteps_alt in H1.
destruct H1 as (n,H1).
apply (SmallStepN_ESmallSteps n (t2et nil t) u); auto.
apply eclos_t2et; simpl; auto.
red; intros; apply H; auto.
rewrite et2t_t2et; simpl; auto.
unfold do_env_subst.
rewrite <- subst_list_equiv; simpl; auto.
red; inversion 1.
Qed.

(** III) -> I) *)

Lemma SmallSteps_BigStep : forall t u, clos t -> IsValue u -> 
 (t==>u) -> exists v, (nil |= t --> v) /\ v2t v = u.
Proof.
 intros.
 assert (normal u).
 intros r Hr.
 inversion H0; subst; inversion Hr.
 destruct (SmallSteps_ESmallSteps _ _ H H2 H1).
 destruct H3.
 assert (exists v', x = v2et v' /\ v2t v' = u).
  inversion H0; subst; simpl in *.
  destruct x; simpl in *; try discriminate; auto.
  exists VDummy; auto.
  destruct x; simpl in *; try discriminate; auto.
  exists (VClos l t1); split; simpl; auto.
 destruct H5 as (v,(Hv1,Hv2)).
 exists v; split; auto.
 apply ESmallSteps_BigStep.
 subst; auto.
Qed.





(* Pas utile (en tout cas dans cette version simplifiée) *)

Lemma subst_list_iter_commut2 : forall l t u u' n,  
 clos u -> clos u' -> clos_list l -> 
 t[S (S n);;=l][n:=u][n:=u'] = t[n:=u][n:=u'][n;;=l].
Proof.
induction l; simpl; auto; intros.
rewrite clos_list_cons in H1; destruct H1.
rewrite IHl; auto.
f_equal.
do 2 (rewrite <- (subst_commut u u'); auto).
rewrite <- (subst_commut u a); auto.
Qed.

Lemma subst_list_iter_commut3 : forall l l' t n, 
 clos_list l -> clos_list l' -> 
 t[(length l+n);;=l'][n;;=l] = t [n;;=l++l'].
Proof.
induction l; simpl; auto; intros.
rewrite clos_list_cons in H; destruct H; auto.
do 2 (rewrite <- subst_list_iter_commut; auto); f_equal.
replace (S (length l + n)) with (length l + (S n)) by omega; auto.
rewrite clos_list_app; auto.
Qed.

Lemma IsValue_alt : forall t, IsValue t <-> exists v, v2t v=t.
Proof. 
 split; intros.
 induction H; auto; intros.
 exists VDummy; auto.
 exists (VClos nil t); simpl; auto.
 destruct H as (v,Hv).
 subst; apply IsValue_v2t.
Qed.
