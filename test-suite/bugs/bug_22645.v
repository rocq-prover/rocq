(* -*- coq-prog-args: ("-native-compiler" "no"); -*- *)
(* Native compilation of [ok] below fails because of #16599. *)

Definition ap_real (g1 g2 cont : nat -> Type) (a : nat) : nat -> Type :=
  fun m => match m with O => cont a | S k => g2 k end.
Definition ap_fake (g1 g2 cont : nat -> Type) (a : nat) : nat -> Type :=
  fun m => match m with O => cont a | S k => g1 k end.

(* [fix inner 2; intros a] leaves the body of [inner] with a single lambda,
   so the uniformity analysis has to reduce it. It looked up [actual] one
   binder too far out per body of the nested block, so it read [decoy] (in
   [russell2], [decoy2]) instead. *)

Fail Fixpoint russell (n : nat) : Type :=
  match n with
  | O => True
  | S p =>
      let decoy := ap_fake in
      let actual := ap_real in
      (ltac:(fix inner 2; intros a;
             exact (actual (inner a) (inner (S a)) (fun x => russell x -> False) a))
        : nat -> nat -> Type) p p
  end.

Fail Fixpoint russell2 (n : nat) : Type :=
  match n with
  | O => True
  | S p =>
      let decoy2 := ap_fake in
      let decoy1 := ap_fake in
      let actual := ap_real in
      (ltac:(fix inner1 2 with (inner2 (a m : nat) {struct m} : Type);
             [ intros a;
               exact (actual (inner1 a) (inner1 (S a)) (fun x => russell2 x -> False) a)
             | intros a m; exact (match m with O => True | S k => inner2 a k end) ])
        : nat -> nat -> Type) p p
  end.

(* The same wrong lookup refused this guarded fixpoint: [actual] was read as
   [p]. *)
Fixpoint ok (n : nat) : Type :=
  match n with
  | O => True
  | S p =>
      let actual := ap_real in
      (ltac:(fix inner 2; intros a;
             exact (actual (inner a) (inner (S a)) (fun _ => ok p) a))
        : nat -> nat -> Type) p p
  end.

(*
Definition diagonal (x : russell 2) : False := x x.
Definition contradiction : False := diagonal diagonal.
Print Assumptions contradiction.
Definition diagonal2 (x : russell2 2) : False := x x.
Definition contradiction2 : False := diagonal2 diagonal2.
Print Assumptions contradiction2.
*)
