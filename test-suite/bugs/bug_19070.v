Set Definitional UIP.

Inductive test : nat -> SProp := T : test 0.

Polymorphic Definition bla@{s;+} (A:nat -> Type@{s;_}) (x:A 0) (y:nat) (e:test y) : A y
  := match e with T => x end.

Arguments bla /.

Definition blo := Eval lazy in bla@{SProp;_}.
Definition bli := Eval lazy in bla@{Type;_}.

Definition blocbv := Eval cbv in bla@{SProp;_}.
Definition blicbv := Eval cbv in bla@{Type;_}.

Definition blosimpl := Eval simpl in bla@{SProp;_}.
Definition blisimpl := Eval simpl in bla@{Type;_}.

Definition blocbn := Eval cbn in bla@{SProp;_}.
Definition blicbn := Eval cbn in bla@{Type;_}.
