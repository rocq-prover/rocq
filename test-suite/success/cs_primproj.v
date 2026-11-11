(* Canonical structure inference with primitive projections: a primitive
   projection [r.(p)], its unfolded form and the application [p params r] of
   its compatibility constant are the same canonical projection and the same
   value. *)

Set Primitive Projections.
Record S := Pack { sort : Type; op : sort -> sort }.
Record T (n : nat) := PackT { tsort : Type; top : tsort -> tsort }.
Unset Primitive Projections.
Arguments tsort {n}.
Arguments top {n}.

(* [tsort t] as the application of the compatibility constant *)
Abbreviation csort t :=
  ltac:(let c := eval cbv beta in ((fun f : T _ -> Type => f t) (@tsort _)) in exact c)
  (only parsing).
(* [sort s] as an unfolded primitive projection *)
Abbreviation usort s :=
  ltac:(let c := eval cbv delta [sort] in (sort s) in exact c)
  (only parsing).

Module ConstKey.
  (* The key of the instance is a compatibility constant application *)
  Definition T_to_S n (t : T n) : S :=
    Eval cbv beta in
    Pack ((fun f : T n -> Type => f t) (@tsort n))
         ((fun f : forall t : T n, tsort t -> tsort t => f t) (@top n)).
  Canonical T_to_S.

  (* against a primitive projection *)
  Check fun n (t : T n) (x : tsort t) => op _ x : tsort t.
  (* against a compatibility constant application *)
  Check fun n (t : T n) (x : csort t) => op _ x : csort t.
End ConstKey.

Module ProjKey.
  (* The key of the instance is a primitive projection *)
  Canonical T_to_S n (t : T n) : S := Pack (tsort t) (top t).

  Check fun n (t : T n) (x : tsort t) => op _ x : tsort t.
  Check fun n (t : T n) (x : csort t) => op _ x : csort t.

  (* The canonical projection is an unfolded primitive projection *)
  Goal forall n (t : T n) (x : tsort t), True.
  Proof.
    intros n t x.
    let s := open_constr:(_ : S) in
    let ty := constr:(usort s) in
    assert (y : ty) by exact x.
    exact I.
  Qed.

  (* Both sides are unfolded primitive projections *)
  Goal forall n (t : T n) (x : tsort t), True.
  Proof.
    intros n t x.
    let s := open_constr:(_ : S) in
    let ty := constr:(usort s) in
    let ty' := eval cbv delta [tsort] in (tsort t) in
    assert (y : ty) by exact (x : ty').
    exact I.
  Qed.
End ProjKey.

(* Coercion classes: the application of the compatibility constant of a
   primitive projection is in the class of the projection *)
Module Coercions.
  Definition el : forall n (t : T n), csort t -> Type := fun _ _ _ => nat.
  Coercion el : tsort >-> Sortclass.
  Check fun n (t : T n) (x : tsort t) (y : x) => y.
  Check fun n (t : T n) (x : csort t) (y : x) => y.
End Coercions.
