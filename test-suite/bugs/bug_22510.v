(* Proof of False from propositional extensionality alone, exploiting the fact
   that module subtyping does not check mind_nparams_rec. *)
Unset Elimination Schemes.

Axiom prop_ext : forall P Q : Prop, (P <-> Q) -> P = Q.

Module Type SIG.
  (* nparams_uniform = 1: the recursive occurrence repeats the parameter *)
  Inductive box (F : unit -> Prop) : Prop :=
  | Box (_ : F tt)
  | Box2 (_ : False) (_ : box F).
End SIG.

Module M.
  (* nparams_uniform = 0: "fun u => F u" is eta-equal to F, but not syntactically
     the parameter, so the uniformity analysis gives up. *)
  Inductive box (F : unit -> Prop) : Prop :=
  | Box (_ : F tt)
  | Box2 (_ : False) (_ : box (fun u => F u)).
End M.

Module F (X : SIG).
  (* legal here: X.box has 1 uniform parameter, so nesting is allowed *)
  Inductive True2 : Prop := I2 (_ : X.box (fun _ => False -> True2)).
End F.

(* M is a subtype of SIG (constructor types agree up to eta) *)
Fail Module G := F M.
(* ... but now G.True2 is nested in M.box, which has 0 uniform parameters *)

(*
Definition unbox (F : unit -> Prop) (b : M.box F) : F tt :=
  match b with M.Box _ x => x | M.Box2 _ e _ => False_ind _ e end.

Definition Heq : (False -> G.True2) <-> G.True2 :=
  conj (fun g => G.I2 (M.Box _ g)) (fun x _ => x).

(* Accepted by the guard checker: with mind_nparams_rec = 0, the commutative-cut
   fast path in Inductive.has_constant_parameters believes that no parameter of
   M.box can depend on the variables bound by the return clause, and skips the
   recargs-tree pruning that should have rejected this. *)
Fixpoint con (x : G.True2) {struct x} : False :=
  match x with
  | G.I2 g =>
      con (unbox (fun _ => G.True2)
             (match prop_ext _ _ Heq in _ = T return M.box (fun _ => T) with
              | eq_refl => g
              end))
  end.

Definition boom : False := con (G.I2 (M.Box _ (fun h : False => False_ind _ h))).
Print Assumptions boom.
*)
