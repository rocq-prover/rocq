Sort s.
Sort s'.

Fail Check fun (A:Univ@{s;Set}) => A : Univ@{s';_}.

Fail Check fun (A:Univ@{s;Set}) => A : Type.

Fail Check fun (A:Set) => A : Univ@{s;_}.

Check fun (A:Univ@{s;Set}) => A : Univ@{s;_}.

Sort S1.

Section S.
  Fail Sort S2.
  Local Set Universe Polymorphism.
  Sort S2.

  Axiom foo : Univ@{S1;Set} -> Univ@{S2;Set}.
  Check foo.
End S.

About foo.
Set Printing Universes.
About foo.

Check foo : _ -> SProp.
Check foo : _ -> Set.

Fail Check foo : SProp -> _.
Fail Check foo : Set -> _.
Check foo : Univ@{S1;Set} -> Set.

Module Type T.
  Module M.
    Fail Sort foz.
  End M.
End T.
