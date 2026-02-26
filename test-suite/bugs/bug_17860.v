Axiom Reduction_sum : forall {A}, nat -> nat -> nat -> (nat -> A) -> A.
#[local] Notation "'einsum_partλ0' s => body"
  := (fun s => Reduction_sum 0 s 1 (fun s => body))
       (at level 10, s binder, body at level 200, only parsing).
#[local] Notation "'einsum_partλ' s1 .. sn => body"
  := (einsum_partλ0 s1 => .. (einsum_partλ0 sn => body) .. )
       (at level 10, s1 binder, sn binder, body at level 200, only parsing).
