Inductive ptrie (A: Type): Type :=
| Empty: ptrie A
| Leaf  : ptrie A.

Definition merge (s t: ptrie unit) : ptrie unit :=
  let merge_aux t :=
    match s , t with
    | Empty _ , t  => t
    | t, Empty _  => t
    | Leaf _ , t => Leaf _
    end in
  merge_aux t.

Goal merge (Leaf _) (Empty _) = Leaf _.
Proof. reflexivity. Qed.

Check fun (s : unit) (t : s = s) =>
  match s, t with
  | tt as t, eq_refl _ => t
  end : unit.
