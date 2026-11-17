Require Import Ltac2.Ltac2.

(* Typing a primitive projection [r.(p)] when the type of [r] is still an
   evar refines that evar to the record type of [p] applied to unknown
   parameters, as typing an application refines the unknown type of its
   function to a product. *)

Set Primitive Projections.
Record R (A : Type) (n : nat) := mk { val : A; prf : val = val }.
Unset Primitive Projections.

Ltac2 proj_of (r : Std.reference) : projection :=
  match r with
  | Std.ConstRef c => Option.get (Proj.of_constant c)
  | _ => Control.throw Assertion_failure
  end.

Ltac2 proj (p : projection) (r : constr) : constr :=
  Constr.Unsafe.make (Constr.Unsafe.Proj p Constr.Relevance.relevant r).

Ltac2 check (c : constr) : constr :=
  match Constr.Unsafe.check c with
  | Val c => c
  | Err e => Control.throw e
  end.

(* A record of unknown type *)
Goal True.
Proof.
  let r := open_constr:(_) in
  (* The type of [r] is an evar *)
  (if Constr.is_evar (Constr.type r) then () else Control.throw Assertion_failure);
  let c := check (proj (proj_of reference:(val)) r) in
  (* It is now [R ?A ?n], and [r.(val) : ?A] *)
  lazy_match! Constr.type r with
  | R ?a ?n =>
    (if Constr.is_evar a then () else Control.throw Assertion_failure);
    (if Constr.is_evar n then () else Control.throw Assertion_failure);
    (if Constr.equal (Constr.type c) a then () else Control.throw Assertion_failure)
  end;
  (* The parameters are found by unification *)
  let r' := constr:(mk bool 0 true eq_refl) in
  Std.unify r r';
  (if Constr.equal (Constr.type c) constr:(bool) then () else Control.throw Assertion_failure).
  exact I.
Qed.

(* A projection whose type depends on the record *)
Goal True.
Proof.
  let r := open_constr:(_) in
  let c := check (proj (proj_of reference:(prf)) r) in
  lazy_match! Constr.type c with
  | @eq ?a _ _ =>
    lazy_match! Constr.type r with
    | R ?a' _ => (if Constr.equal a a' then () else Control.throw Assertion_failure)
    end
  end;
  Std.unify r constr:(mk nat 0 1 eq_refl);
  Std.unify (Constr.type c) constr:(1 = 1).
  exact I.
Qed.

(* The parameters live in the context of the evar standing for the type of
   the record *)
Goal forall (b : bool) (r : R bool 0), True.
Proof.
  intros b.
  let r := open_constr:(_) in
  intros r0;
  let c := check (proj (proj_of reference:(val)) r) in
  lazy_match! Constr.type r with
  | R _ ?n =>
    (* As [r], [?n] can depend on [b] but not on [r0] *)
    match Control.case (fun () => Std.unify n constr:(if val _ _ &r0 then 0 else 1)) with
    | Val _ => Control.throw Assertion_failure
    | Err _ => ()
    end;
    Std.unify n constr:(if &b then 0 else 0)
  end;
  Std.unify r open_constr:(mk bool _ &b eq_refl);
  (if Constr.equal (Constr.type c) constr:(bool) then () else Control.throw Assertion_failure).
  exact I.
Qed.

(* A term whose type is not an inductive type is still an error *)
Goal forall f : nat -> nat, True.
Proof.
  intros f.
  match Constr.Unsafe.check (proj (proj_of reference:(val)) constr:(f)) with
  | Val _ => Control.throw Assertion_failure
  | Err _ => ()
  end.
  exact I.
Qed.
