Require Import Ltac2.Ltac2.
Require Import Ltac2.Option.

(** Test Ind.scheme_lookup *)

Ltac2 Eval
  let nat := Option.get (Env.get [@Corelib; @Init; @Datatypes; @nat]) in
  let nat := match nat with
  | Std.IndRef ind => ind
  | _ => Control.throw Not_found
  end in
  (* nat should have a rect_dep scheme (i.e., nat_rect) *)
  match Ind.scheme_lookup Ind.rect_dep nat with
  | Some _ => ()
  | None => Control.throw Not_found
  end.

Ltac2 Eval
  let nat := Option.get (Env.get [@Corelib; @Init; @Datatypes; @nat]) in
  let nat := match nat with
  | Std.IndRef ind => ind
  | _ => Control.throw Not_found
  end in
  (* nat should have an ind_dep scheme (i.e., nat_ind) *)
  match Ind.scheme_lookup Ind.ind_dep nat with
  | Some _ => ()
  | None => Control.throw Not_found
  end.
