(* Regression tests for alias refolding after real iota progress.

   A transparent alias such as [fst_nat] may be refolded when reduction is
   genuinely stuck, but it must not be kept once an argument has reduced enough
   to expose a new term by iota.  The expected output is the behavior of
   master: the aliases below disappear after the selected branch is reduced. *)

Set Printing Width 200.

Definition id_nat (x : nat) := x.
Definition fst_nat (x y : nat) := x.
Definition snd_nat (x y : nat) := y.
Definition third_nat (x y z : nat) := z.
Definition pick3 (a b c d : nat) := c.
Definition fst4 (a b c d : nat) := a.
Definition pick4 (a b c d : nat) := d.
Definition wrap2 (x y : nat) := y.

Eval cbn in
  (fun y : nat =>
     (fun z : nat =>
        fst_nat
          (match z with
           | O => match y with O => S O | S _ => O end
           | S _ => O
           end)
          O)
       O).

Eval cbn in
  (fun y : nat =>
     (fun z : nat =>
        snd_nat
          O
          (match z with
           | O => match y with O => S O | S _ => O end
           | S _ => O
           end))
       O).

Eval cbn in
  (fun y : nat =>
     (fun z : nat =>
        third_nat
          O
          O
          (match z with
           | O => match y with O => S O | S _ => O end
           | S _ => O
           end))
       O).

Eval cbn in
  (fun y : nat =>
     id_nat
       (match true with
        | true => match y with O => S O | S _ => O end
        | false => O
        end)).

Eval cbn in
  (fun y : nat =>
     pick3
       O
       (S O)
       (match true with
        | true => match y with O => S O | S _ => O end
        | false => O
        end)
       (S (S O))).

Eval cbn in
  (fun y : nat =>
     id_nat (id_nat
       (match true with
        | true => match y with O => S O | S _ => O end
        | false => O
        end))).

Eval cbn in
  (fun y : nat =>
     fst4
       (match true with
        | true => match y with O => S O | S _ => O end
        | false => O
        end)
       O O O).

Eval cbn in
  (fun y : nat =>
     pick4 O O O
       (match true with
        | true => match y with O => S O | S _ => O end
        | false => O
        end)).

Eval cbn in
  (fun y : nat =>
     S (id_nat
          (match true with
           | true => match y with O => S O | S _ => O end
           | false => O
           end))).

Eval cbn in
  (fun y : nat =>
     wrap2
       (if true then O else S O)
       (match true with
        | true => match y with O => S O | S _ => O end
        | false => O
        end)).
