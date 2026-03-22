Require Import Ltac2.Ltac2.
Require Import Ltac2.Option.

(** Test Ind.Scheme.lookup *)

Ltac2 Eval
  let nat := Option.get (Env.get [@Corelib; @Init; @Datatypes; @nat]) in
  let nat := match nat with
  | Std.IndRef ind => ind
  | _ => Control.throw Not_found
  end in
  (* nat should have a rect_dep scheme (i.e., nat_rect) *)
  match Ind.Scheme.lookup Ind.Scheme.rect_dep nat with
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
  match Ind.Scheme.lookup Ind.Scheme.ind_dep nat with
  | Some _ => ()
  | None => Control.throw Not_found
  end.
