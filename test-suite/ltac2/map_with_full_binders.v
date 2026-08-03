Require Import Ltac2.Ltac2.
Import Constr.Unsafe.

(** Helper: check two constrs are equal, raise informative error if not *)
Local Ltac2 assert_constr_equal (msg : string) (expected : constr) (actual : constr) :=
  if Constr.equal expected actual then ()
  else Control.throw (Invalid_argument (Some (Message.concat
    (Message.of_string msg)
    (Message.concat (Message.of_string ": expected ")
    (Message.concat (Message.of_constr expected)
    (Message.concat (Message.of_string " but got ")
    (Message.of_constr actual))))))).

(** Test 1: identity map on various term shapes preserves the term *)
Goal True.
  (* Lambda *)
  let c := '(fun x : nat => x) in
  let c' := Constr.map_with_full_binders (fun x => x) c in
  assert_constr_equal "Lambda identity" c c';

  (* Prod *)
  let c := '(forall x : nat, x = x) in
  let c' := Constr.map_with_full_binders (fun x => x) c in
  assert_constr_equal "Prod identity" c c';

  (* LetIn *)
  let c := '(let x : nat := 0 in x) in
  let c' := Constr.map_with_full_binders (fun x => x) c in
  assert_constr_equal "LetIn identity" c c';

  (* App *)
  let c := '(S (S O)) in
  let c' := Constr.map_with_full_binders (fun x => x) c in
  assert_constr_equal "App identity" c c';

  (* Constant *)
  let c := 'Nat.add in
  let c' := Constr.map_with_full_binders (fun x => x) c in
  assert_constr_equal "Constant identity" c c';

  (* App of const *)
  let c := '(negb true) in
  let c' := Constr.map_with_full_binders (fun x => x) c in
  assert_constr_equal "App of const identity" c c';

  exact I.
Qed.

(** Test 2: mapping a transformation through Lambda *)
Goal True.
  let c := '(fun x : nat => x) in
  let c' := Constr.map_with_full_binders (fun t =>
    match Constr.equal t 'nat with
    | true => 'bool
    | false => t
    end) c in
  let expected := '(fun x : bool => x) in
  assert_constr_equal "Lambda nat->bool" expected c';
  exact I.
Qed.

(** Test 3: mapping a transformation through Prod *)
Goal True.
  (* Map on immediate subterms of a Prod: the binder type and the body.
     Use a body that does not mention the binder variable so that
     changing the binder type does not create a type mismatch. *)
  let c := '(forall x : nat, True) in
  let c' := Constr.map_with_full_binders (fun t =>
    match Constr.equal t 'nat with
    | true => 'bool
    | false => t
    end) c in
  let expected := '(forall x : bool, True) in
  assert_constr_equal "Prod nat->bool" expected c';
  exact I.
Qed.

(** Test 4: mapping through LetIn *)
Goal True.
  let c := '(let x : nat := 0 in x) in
  let c' := Constr.map_with_full_binders (fun t =>
    match Constr.equal t '0 with
    | true => '1
    | false => t
    end) c in
  let expected := '(let x : nat := 1 in x) in
  assert_constr_equal "LetIn 0->1" expected c';
  exact I.
Qed.

(** Test 5: mapping through App *)
Goal True.
  let c := '(Nat.add 0 1) in
  let c' := Constr.map_with_full_binders (fun t =>
    match Constr.equal t '0 with
    | true => '2
    | false => t
    end) c in
  let expected := '(Nat.add 2 1) in
  assert_constr_equal "App 0->2" expected c';
  exact I.
Qed.

(** Test 6: mapping through Fix *)
Goal True.
  let c := '(fix add (n m : nat) : nat :=
    match n with
    | O => m
    | S p => S (add p m)
    end) in
  let c' := Constr.map_with_full_binders (fun x => x) c in
  assert_constr_equal "Fix identity" c c';
  exact I.
Qed.

(** Test 7: non-recursive: f is applied only to immediate subterms *)
Goal True.
  (* For a Lambda, f is applied to the binder type and the body.
     If we map nat->bool on (fun x : nat => (fun y : nat => y)),
     only the outer nat and the body (fun y : nat => y) are touched.
     The inner (fun y : nat => y) is not recursively processed. *)
  let c := '(fun x : nat => (fun y : nat => y)) in
  let c' := Constr.map_with_full_binders (fun t =>
    match Constr.equal t 'nat with
    | true => 'bool
    | false => t
    end) c in
  (* Only the outer binder type nat should change to bool.
     The body (fun y : nat => y) is passed to f which sees it as a whole
     and since it's not equal to nat, it's returned unchanged. *)
  let expected := '(fun x : bool => (fun y : nat => y)) in
  assert_constr_equal "non-recursive Lambda" expected c';
  exact I.
Qed.
