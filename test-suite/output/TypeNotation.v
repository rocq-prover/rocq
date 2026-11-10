(* A notation mentioning an anonymous [Type] prints back (from MetaRocq's param_cheap_packed) *)
#[universes(template)]
Record sigma A B := mk_sig { π1 : A ; π2 : B π1 }.
Notation "'∃' x .. y , p" := (sigma _ (fun x => .. (sigma _ (fun y => p)) ..))
  (at level 10, x binder, p at level 200, right associativity).
Notation "'TYPE'" := (sigma Type (fun A => A -> Type)).
Check (fun (A : TYPE) => A).
Definition foo (A : TYPE) := A.
Check foo.
(* With Printing Universes, the universes do not match the notation's [Type] *)
Set Printing Universes.
Check foo.
