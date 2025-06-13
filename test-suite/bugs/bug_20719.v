CoInductive strm := { hd : nat; tl : strm }.

Definition foobar (i : unit) :=
  cofix seq n := {| hd := match i with tt => n end; tl := seq (S n) |}.

CoFixpoint seq n := {| hd := n; tl := seq (S n) |}.

Check (@eq_refl (nat -> strm) seq) <<: foobar tt = seq.
Check (@eq_refl (nat -> strm) seq) <: foobar tt = seq.

Check eq_refl 5 <<: hd (foobar tt 5) = 5.
Check eq_refl 5 <: hd (foobar tt 5) = 5.

Check eq_refl 5 <<: hd (seq 5) = 5.
Check eq_refl 5 <: hd (seq 5) = 5.

CoFixpoint dummy (i : bool) := {| hd := 0; tl := dummy i |}.

Fail Check (eq_refl (dummy true)) <: (dummy true) = (dummy false).
Fail Check (eq_refl (dummy true)) <<: (dummy true) = (dummy false).

Set Warnings "-non-recursive".

CoInductive lazy T := Lazy : T -> lazy T.
CoFixpoint of_fun {T} f := Lazy T (f tt).
Definition force {T} v : T := match v with Lazy _ v => v end.

Check eq_refl 42 <<: (force (of_fun (fun _ => 42))) = 42.
Check eq_refl 42 <: (force (of_fun (fun _ => 42))) = 42.
