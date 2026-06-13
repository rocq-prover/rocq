(* after an iota step exposes a stuck recursive call below an alias/projection,
   [cbn] must not refold the alias. *)

Module PCUIC.
  (* Minimized from metarocq's PCUICUnivSubstitutionConv.v *)

  Inductive idx : Set := izero | isucc (_ : idx).
  Inductive seq (A : Type) : Type := snil | scons (_ : A) (_ : seq A).
  Inductive maybe (A : Type) : Type := nothing | just (_ : A).

  Inductive level : Set := lzero | lname (_ : idx) | lvar (_ : idx).
  Record expr : Set := mkexpr { expr_level : level; expr_offset : idx }.

  Definition expr_succ (e : expr) : expr :=
    mkexpr (expr_level e) (isucc (expr_offset e)).

  Fixpoint lookup {A : Type} (xs : seq A) (i : idx) : maybe A :=
    match xs, i with
    | snil _, _ => nothing _
    | scons _ x _, izero => just _ x
    | scons _ _ xs, isucc i => lookup xs i
    end.

  Class Subst (A : Type) := subst : seq level -> A -> A.
  Arguments subst {_ _} _ _.
  Notation "x @[ u ]" := (subst u x) (at level 1, format "x @[ u ]").

  #[global] Instance subst_expr : Subst expr :=
    fun u e =>
      match e with
      | mkexpr lzero _ | mkexpr (lname _) _ => e
      | mkexpr (lvar i) n =>
        match lookup u i with
        | just _ l => mkexpr l n
        | nothing _ => mkexpr lzero n
        end
      end.

  Lemma cbn_exposes_stuck_discriminant (u : seq level) (y : expr) :
    (expr_succ y)@[u] = expr_succ (y@[u]).
  Proof.
    destruct y as [[] ?]; simpl. all: cbn; auto.
    now destruct lookup.
  Qed.
End PCUIC.

Module Minimal.
  (* Smaller, derived example *)
  Inductive maybe := nothing | just (_ : nat).

  Fixpoint inspect (u : nat) : maybe :=
    match u with O => nothing | S k => inspect k end.

  Definition selected (u e : nat) :=
    match e with
    | O => O
    | S n => match inspect u with nothing => O | just _ => n end
    end.

  Definition alias (f : nat -> nat -> nat) := f.

  Goal True.
  Proof.
    let t := constr:(fun u n => alias selected u (if true then S n else O)) in
    let t := eval cbn in t in
    let s := constr:(fun u n : nat => match inspect u with
                     | nothing => 0
                     | just _ => n
                     end) in
    constr_eq t s.
  Abort.
End Minimal.
