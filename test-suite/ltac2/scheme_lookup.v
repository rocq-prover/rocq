Require Import Ltac2.Ltac2.
Require Import Ltac2.Option.

(** Test Scheme.lookup *)

Ltac2 Eval
  let nat := Option.get (Env.get [@Corelib; @Init; @Datatypes; @nat]) in
  (* nat should have a rect_dep scheme (i.e., nat_rect) *)
  match Scheme.lookup Scheme.rect_dep nat with
  | Some _ => ()
  | None => Control.throw Not_found
  end.

Ltac2 Eval
  let nat := Option.get (Env.get [@Corelib; @Init; @Datatypes; @nat]) in
  (* nat should have an ind_dep scheme (i.e., nat_ind) *)
  match Scheme.lookup Scheme.ind_dep nat with
  | Some _ => ()
  | None => Control.throw Not_found
  end.

Scheme nat_scase := Elimination for nat Sort SProp.
Scheme nat_scase_nodep := Case for nat Sort SProp.

Ltac2 Eval
  let nat := Option.get (Env.get [@Corelib; @Init; @Datatypes; @nat]) in
  (* nat should have an scase_dep scheme after explicit declaration *)
  match Scheme.lookup Scheme.scase_dep nat with
  | Some _ => ()
  | None => Control.throw Not_found
  end.

Ltac2 Eval
  let nat := Option.get (Env.get [@Corelib; @Init; @Datatypes; @nat]) in
  (* nat should have an scase_nodep scheme after explicit declaration *)
  match Scheme.lookup Scheme.scase_nodep nat with
  | Some _ => ()
  | None => Control.throw Not_found
  end.
