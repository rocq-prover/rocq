CoInductive D (X Y : Type) := dc : X -> Y -> D X Y.
CoInductive C (A : Type) := cc : C A -> D (C A) A -> C A.
Inductive I : Type := ic : C I -> I.

Fail
CoFixpoint cycle : C I :=
  (cofix f : C I := cc I f g
   with g : D (C I) I := dc (C I) I cycle (ic cycle)
   for f).

(*
Fixpoint empty (i : I) : False :=
  match i with
  | ic c => match c with
    | cc _ _ d => match d with
      | dc _ _ _ j => empty j
      end
    end
  end.

Definition contradiction : False := empty (ic cycle).
Print Assumptions contradiction.
*)
