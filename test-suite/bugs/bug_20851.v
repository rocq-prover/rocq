Set Implicit Arguments.
Axiom Iso : Type -> Type -> Type.
Axiom rel_iso : forall {A B} (i : Iso A B), Prop.
Axiom any : forall {A}, A.
Existing Class Iso.
Class IsoStatementProofFor {A : Type} (a : A) {isoT : Type} (iso : isoT) := {}.

Lemma foo
  (prod_iso : Iso False False -> Iso True True)
  (x5 : Type)
  (x6 : Type)
  (hx1 : rel_iso (prod_iso any) -> Iso x5 x6)
  (H3 : IsoStatementProofFor x5 hx1)
  : True.
Proof.
  let x :=
    constr:(let dummy := _ : IsoStatementProofFor x5 _ in
            match _ return _ with
            | iso => let _unif := dummy : IsoStatementProofFor x5 iso in
                    iso
            end)
  in
  idtac x.
Abort.
