Goal forall n:nat, n=0 -> {x:{n|n=0/\n=0}| True}.
Proof.
intros.
exists (exist (fun _ => _ /\ _) n (conj H H)).
constructor.
Qed.

Goal forall n:nat, n=0 -> {x:{n|n=0/\n=0}| True}.
Proof.
intros.
exists (exist _ n (conj H H)).
constructor.
Qed.
