Definition dirty (x : bool) : bool :=
  match x with true => true | false => true end.

(* Triggers PUSHACCMANY with first = 0, size = 5 *)
Definition exploit0 : bool :=
  let a := dirty false in
  let b := (let _ := true in a) in
  let c := (let _ := true in b) in
  let d := (let _ := true in c) in
  let e := (let _ := true in d) in
  match e with true => true | false => false end.

Definition exploit0_vm : exploit0 = true :=
  eq_refl true <: exploit0 = true.

Fail Definition exploit0_bad : exploit0 = false :=
  eq_refl false <: exploit0 = false.

(* Triggers PUSHACCMANY with first = 1, size = 4 *)
Definition exploit1 : bool :=
  let a := dirty false in
  let b := (let _ := true in false) in
  let c := (let _ := true in a) in
  let d := (let _ := true in b) in
  let e := (let _ := true in c) in
  let f := (let _ := true in d) in
  match e with true => f | false => true end.

Definition exploit1_vm : exploit1 = false :=
  eq_refl false <: exploit1 = false.

Fail Definition exploit1_bad : exploit1 = true :=
  eq_refl true <: exploit1 = true.
