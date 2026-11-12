(* Compiled against ../donor/Lib.v. With the forged library, F's lemma says
   (F.k, canonical P.X.d) = false, and the application F A rebuilds the
   canonical name from the label k: G's lemma says (G.k, canonical A.X.k)
   = false, which matches T's. *)

Require Import ForgedAliases.Lib.

Module Type T.
  Parameter lemma : eq bool A.X.k false.
End T.

Module G : T := F A.

Definition boom : eq bool true false := G.lemma.

Definition contradiction : False :=
  match boom in eq _ _ y return discr y with
  | eq_refl _ _ => I
  end.
