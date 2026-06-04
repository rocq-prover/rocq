(* cbn is able to refold mutual recursive calls *)

Fixpoint foo (n : nat) :=
  match n with
  | 0 => true
  | S n => g n
  end
with g (n : nat) : bool :=
  match n with
  | 0 => true
  | S n => foo n
  end.
Goal forall n, foo (S n) = g n.
  intros. cbn.
  match goal with
    |- g _ = g _ => reflexivity
  end.
Qed.

(* simpl nomatch *)

Definition thing n := match n with  0 => True | S n => False end.

Arguments thing _ / : simpl nomatch.

Goal forall x, thing x.
  intros. cbn.
  match goal with |- thing x => idtac end.
Abort.

Definition thing' n := n + n.

Arguments thing' !_ / : simpl nomatch.
Lemma bar n : thing' n = 0.
Proof.
  cbn.
  match goal with |- thing' _ = _ => idtac end.
  Arguments thing' _ / : simpl nomatch.
  cbn.
  match goal with |- _ + _ = _ => idtac end.
Abort.

Module MutualFixCoFixInSection.

Section S.
Variable p:nat.
Fixpoint f n := match n with 0 => p | S n => f n + g n end
with g n := match n with 0 => p | S n => f n + g n end.
End S.

Goal forall n, f n (S n) = g 0 (S n).
intros. cbn.
match goal with [ |- f n n + g n n = f 0 n + g 0 n ] => idtac end.
Abort.

CoInductive stream {A:Type} : Type :=
  | scons: A->stream->stream.
Definition stream_unfold {A} (s: @ stream A) := match s with
| scons a s' => (a, scons a s')
end.

Section C.
Variable (x:nat).
CoFixpoint mut_stream1 (n:nat) := scons n (mut_stream2 (n+x))
with mut_stream2 (n:nat) :=  scons n (mut_stream1  (n+x)).
End C.

Goal (forall x n, stream_unfold (mut_stream1 x n) = stream_unfold (mut_stream2 x n)).
intros. cbn.
match goal with [ |- (n, scons n (mut_stream2 x (n + x))) = (n, scons n (mut_stream1 x (n + x))) ] => idtac end.
Abort.

End MutualFixCoFixInSection.

Module RefoldProjectionAlias.

Module AsClass.
  Class Difference A := difference : A -> A -> A.
  Arguments difference : simpl nomatch.
  Definition set := { t : nat | True }.
  Definition set_difference : Difference set := fun X Y =>
    let (t1, _) := X in let (t2, _) := Y in exist _ t1 I.

  Goal forall y : set, True.
  Proof.
    intro y.
    let v := eval cbn in (@difference set set_difference (exist _ 0 I) y) in
    lazymatch v with
    | difference (exist _ 0 I) y => exact I
    | _ => fail "difference was not refolded"
    end.
  Qed.
End AsClass.

Module AsDef.
  Definition Difference A := A -> A -> A.
  Definition difference {A} {D : Difference A} : A -> A -> A := D.
  Arguments difference : simpl nomatch.
  Definition set := { t : nat | True }.
  Definition set_difference : Difference set := fun X Y =>
    let (t1, _) := X in let (t2, _) := Y in exist _ t1 I.

  Goal forall y : set, True.
  Proof.
    intro y.
    let v := eval cbn in (@difference set set_difference (exist _ 0 I) y) in
    lazymatch v with
    | difference (exist _ 0 I) y => exact I
    | _ => fail "difference was not refolded"
    end.
  Qed.
End AsDef.

End RefoldProjectionAlias.

Module RefoldAfterPositiveIota.

Inductive tree (A : Type) :=
| Leaf : tree A
| Node : tree A -> A -> tree A -> tree A.
Arguments Leaf {A}.
Arguments Node {A} _ _ _.

Definition bal {A} (l : tree A) (x : A) (r : tree A) := Node l x r.

Fixpoint remove_min {A} (l : tree A) (x : A) (r : tree A) : tree A * A :=
  match l with
  | Leaf => (r, x)
  | Node ll lx lr =>
    let (l', m) := remove_min ll lx lr in
    (bal l' x r, m)
  end.

Definition merge {A} (s1 s2 : tree A) :=
  match s1, s2 with
  | Leaf, _ => s2
  | _, Leaf => s1
  | _, Node l2 x2 r2 =>
    match remove_min l2 x2 r2 with
    | (s2', x) => bal s1 x s2'
    end
  end.

#[local] Ltac caseq :=
match goal with [ |- context [match ?t with _ => _ end] ] =>
  let cmp := fresh in
  let H := fresh in
  remember t as cmp eqn:H; symmetry in H; destruct cmp
end.

(* The [Node] branch of [merge] exposes a stuck match on the second tree.
   [cbn] must not refold [merge] after making the positive iota step on the
   first tree; otherwise this induction principle is left with open goals. *)
Lemma merge_ind {A : Type} {P : tree A -> tree A -> tree A -> Prop} :
  (forall s1 s2 : tree A, s1 = Leaf -> P Leaf s2 s2) ->
  (forall (s1 s2 l1 : tree A) (x1 : A) (r1 : tree A),
   s1 = Node l1 x1 r1 -> s2 = Leaf -> P (Node l1 x1 r1) Leaf s1) ->
  (forall (s1 s2 l1 : tree A) (x1 : A) (r1 : tree A),
   s1 = Node l1 x1 r1 ->
   forall (l2 : tree A) (x2 : A) (r2 : tree A),
   s2 = Node l2 x2 r2 ->
   forall (s2' : tree A) (x : A),
   remove_min l2 x2 r2 = (s2', x) ->
   P (Node l1 x1 r1) (Node l2 x2 r2) (bal s1 x s2')) ->
  forall s1 s2 : tree A, P s1 s2 (merge s1 s2).
Proof.
intros; induction s1; cbn; repeat caseq; eauto.
Qed.

End RefoldAfterPositiveIota.
