Require BinNums.

(* TODO tests that declaring a type that doesn't look like nat with
   primitive_nat is rejected

   and that multiple primitive_nat types are rejected
   (or make it supported then test that) *)

#[primitive_nat]
Inductive N : Set := O | S (_:N).

Fixpoint add n m {struct n} :=
  match n with
  | O => m
  | S k => S (add k m)
  end where "a + b" := (add a b) : nat_scope.

Fixpoint mul n m {struct n} :=
  match n with
  | O => O
  | S p => m + p * m
  end where "a * b" := (mul a b) : nat_scope.

Fixpoint tail_add n m :=
  match n with
    | O => m
    | S n => tail_add n (S m)
  end.

Fixpoint tail_addmul r n m :=
  match n with
    | O => r
    | S n => tail_addmul (tail_add m r) n m
  end.

Definition tail_mul n m := tail_addmul O n m.

Local Abbreviation ten_raw := (S (S (S (S (S (S (S (S (S (S O)))))))))).
Local Abbreviation ten := ltac:(let c := constr:(ten_raw) in let c := eval cbv in c in exact c) (only parsing).

Fixpoint of_uint_acc (d:Decimal.uint)(acc:N) :=
  match d with
  | Decimal.Nil => acc
  | Decimal.D0 d => of_uint_acc d (tail_mul ten acc)
  | Decimal.D1 d => of_uint_acc d (S (tail_mul ten acc))
  | Decimal.D2 d => of_uint_acc d (S (S (tail_mul ten acc)))
  | Decimal.D3 d => of_uint_acc d (S (S (S (tail_mul ten acc))))
  | Decimal.D4 d => of_uint_acc d (S (S (S (S (tail_mul ten acc)))))
  | Decimal.D5 d => of_uint_acc d (S (S (S (S (S (tail_mul ten acc))))))
  | Decimal.D6 d => of_uint_acc d (S (S (S (S (S (S (tail_mul ten acc)))))))
  | Decimal.D7 d => of_uint_acc d (S (S (S (S (S (S (S (tail_mul ten acc))))))))
  | Decimal.D8 d => of_uint_acc d (S (S (S (S (S (S (S (S (tail_mul ten acc)))))))))
  | Decimal.D9 d => of_uint_acc d (S (S (S (S (S (S (S (S (S (tail_mul ten acc))))))))))
  end.

Definition of_uint (d:Decimal.uint) := of_uint_acc d O.

Definition of_num_uint (d:Number.uint) :=
  match d with
  | Number.UIntDecimal d => Some (of_uint d)
  | Number.UIntHexadecimal d => None
  end.

Fixpoint to_little_uint n acc :=
  match n with
  | O => acc
  | S n => to_little_uint n (Decimal.Little.succ acc)
  end.

Definition to_uint n :=
  Decimal.rev (to_little_uint n Decimal.zero).

Fixpoint sub (n m:N) {struct n} : N :=
  match n, m with
  | O, _ => n
  | S k, O => n
  | S k, S l => k - l
  end
where "a - b" := (sub a b).

Register sub as cbv.sub.

Fixpoint div2r (n:N) :=
  match n with
  | O | S O => n
  | S (S k) => S (div2r k)
  end.

Register div2r as cbv.div2r.

Definition div2 n := n - div2r n.

Definition rem2 n := n - (let x := div2 n in x + x).

Section S.
  (* NB: p0 is not part of the recursion ([div2 (S (S n))] is never 0).
     It's only used when the fixpoint is directly called on 0. *)
  Variables (P:N -> Type) (p0 : P O) (p1 : P (S O)) (p2 : forall n, P (div2 (S (S n))) -> P (S (S n))).

  Fixpoint rec2 n :=
    match n return P n with
    | O => p0
    | S k =>
        match k as k' return k = k' -> P (S k') with
        | O => fun _ => p1
        | S l =>
            fun e : k = S l =>
              p2 l
                (match e in _ = x return P (x - div2r l) with
                 | eq_refl => rec2 (k - div2r l)
                 end)
        end eq_refl
    end.
End S.

Section to_bin.
  (* section for the import for convenience *)
  Abbreviation myN := N.
  Import BinNums.

  (* returns xH for 0 *)
  Definition to_positive (n:myN) : BinNums.positive :=
    rec2 (fun _ => positive) xH xH
      (fun n x => (* x = div2 (2+n), we need to produce 2+n = 2*x + rem2 (2+n) *)
         match rem2 (S (S n)) with
         | O => xO x
         | S _ => xI x
         end)
      n.

  Definition to_Z n :=
    match n with
    | O => Z0
    | S _ => Zpos (to_positive n)
    end.
End to_bin.

Number Notation N of_num_uint to_Z (abstract after 5000) : nat_scope.

(* printing needs add to be registered to be fast (used in rem2) *)
Set Printing All.

Time Eval cbv in 5000000.
(* without bignat, stack overflows
   with bignat, 0.8s
   (time seems about linear in n, ie exponential in the size of the decimal representation)
*)

Time Eval cbv in 1000 * 1000.
(* without bignat, stack overflows
   with bignat, 0.1s *)

Register add as cbv.add.

Unset Printing All.

Time Eval cbv in 5000000.
(* still 0.8s *)

Time Eval cbv in 1000 * 1000.
(* instant (add used in mul) *)

Register mul as cbv.mul.

Time Eval cbv in 200 * 200 * 200 * 200 * 200 * 200 * 200 * 200.
(* instant (stack overflow without registered mul) *)

Register tail_mul as cbv.tail_mul.
(* makes parsing fast *)

Time Eval cbv in 5000000.
(* instant *)
Time Eval cbv in 50000000.
(* also instant *)
Time Eval cbv in 500000000000000000000000000.
(* still instant *)

Definition pred n := match n with S k => k | 0 => 0 end.

Check eq_refl 0 : pred (pred 1) = 0.

Time Eval lazy in pred ltac:(let c := eval cbv in 500000000 in exact c).
(* instant (but big + 1 would stack overflow) *)

(* for testing non registered mul with registered add *)
Fixpoint mymul n m :=
  match n with
  | O => O
  | S p => m + mymul p m
  end.

Notation "x ** y" := (mymul x y) (at level 41, right associativity).

Time Eval cbv in 200 ** 200000000.
(* instant *)

Time Eval cbv in 200 ** 200 ** 200 ** 200 ** 200 ** 200 ** 200 ** 200.
(* right associativity very important here: it means we have 200 * 7 recursions in mymul
   instead of 200 ^ 7 *)

Definition vmtwo := Eval vm_compute in 1 + 1.
Check eq_refl : vmtwo = 2.
Check eq_refl 4 <: vmtwo + 2 = 4.

Definition vmSS x := Eval vm_compute in S (S x).
Check eq_refl : vmSS = fun x => S (S x).

(* 4611686018427387903 = int63 max_int *)
Definition vmbig := Eval vm_compute in 2 + 4611686018427387903.
Check eq_refl : vmbig = 4611686018427387905.
Check eq_refl vmbig <: vmbig = 4611686018427387905.
Check eq_refl (S vmbig) <: S vmbig = 4611686018427387906.

Definition nativetwo := Eval native_compute in 1 + 1.
Check eq_refl : nativetwo = 2.
Check eq_refl 4 <<: nativetwo + 2 = 4.

Definition nativeSS x := Eval native_compute in S (S x).
Check eq_refl : nativeSS = fun x => S (S x).

(* 4611686018427387903 = int63 max_int *)
Definition nativebig := Eval native_compute in 2 + 4611686018427387903.
Check eq_refl : nativebig = 4611686018427387905.
Check eq_refl nativebig <<: nativebig = 4611686018427387905.
Check eq_refl (S nativebig) <<: S nativebig = 4611686018427387906.

Check eq_refl 0 <: pred (pred 1) = 0.
Check eq_refl 0 <<: pred (pred 1) = 0.

Check eq_refl 4611686018427387900 : 4611686018427387900 = pred (pred (pred 4611686018427387903)).
Check eq_refl 4611686018427387900 <: 4611686018427387900 = pred (pred (pred 4611686018427387903)).
Check eq_refl 4611686018427387900 <<: 4611686018427387900 = pred (pred (pred 4611686018427387903)).

Check eq_refl 4611686018427387900 : 4611686018427387900 = pred (pred (pred (pred (pred (pred (3 + 4611686018427387903)))))).
Check eq_refl 4611686018427387900 <: 4611686018427387900 = pred (pred (pred (pred (pred (pred (3 + 4611686018427387903)))))).
Check eq_refl 4611686018427387900 <<: 4611686018427387900 = pred (pred (pred (pred (pred (pred (3 + 4611686018427387903)))))).

(* some large number from keyboard mashing (all commands instant including printing) *)
(* results checked in python 3.13.12 (compute "n * m",
   "len(bin(n * m)) - 2" (-2 because starts with "0b")
   and "(n * m).bit_count()" *)
Definition large := Eval cbv in 534653679184394009346 * 4576931832291539343426.
Check eq_refl : large = 2447073443510841321595526374542420547659396.

Definition nbits := rec2 (fun _ => N) 0 1 (fun _ x => S x).
Definition largebits := Eval cbv in nbits large.
Check eq_refl : largebits = 141.

(* NB [rem2 (S (S n)) = rem2 n] *)
Definition popcount := rec2 (fun _ => N) 0 1 (fun n x => x + rem2 n).
Definition largecnt := Eval cbv in popcount large.
Check eq_refl : largecnt = 69.

Goal forall n:N, 0 = n -> 1 = S n.
Proof.
  intros n H.
  rewrite H.
  reflexivity.
Qed.

Goal 1 = 2 -> False.
  congruence.
Qed.

Goal forall x, S x = 1 -> x = 0.
  intros.
  match goal with h : ?f _ = ?f _ |- _ => injection h as h end.
  exact H.
Qed.

Definition ignore (x y:N) := x.

Check eq_refl : ignore 1 _ = 1.

Require Import ssreflect.

Lemma test (P:N -> bool) : is_true (P 0).
Proof.
  elim: 0.
Abort.
