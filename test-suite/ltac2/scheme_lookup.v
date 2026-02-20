Require Import Ltac2.Ltac2.
Require Import Ltac2.Option.

(** Test Ind.scheme_kind_exists *)

Ltac2 Eval
  (* "rect_dep" is a standard elimination scheme kind *)
  if Ind.scheme_kind_exists "rect_dep" then ()
  else Control.throw Not_found.

Ltac2 Eval
  (* An invalid scheme kind should return false *)
  if Ind.scheme_kind_exists "nonexistent_scheme_kind" then
    Control.throw Not_found
  else ().

(** Test Ind.scheme_lookup *)

Ltac2 Eval
  let nat := Option.get (Env.get [@Corelib; @Init; @Datatypes; @nat]) in
  let nat := match nat with
  | Std.IndRef ind => ind
  | _ => Control.throw Not_found
  end in
  (* nat should have a rect_dep scheme (i.e., nat_rect) *)
  match Ind.scheme_lookup "rect_dep" nat with
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
  match Ind.scheme_lookup "ind_dep" nat with
  | Some _ => ()
  | None => Control.throw Not_found
  end.

Ltac2 Eval
  let nat := Option.get (Env.get [@Corelib; @Init; @Datatypes; @nat]) in
  let nat := match nat with
  | Std.IndRef ind => ind
  | _ => Control.throw Not_found
  end in
  (* A bogus scheme kind should return None *)
  match Ind.scheme_lookup "nonexistent_scheme_kind" nat with
  | Some _ => Control.throw Not_found
  | None => ()
  end.

(** Test Ind.scheme_find *)

Ltac2 Eval
  let bool := Option.get (Env.get [@Corelib; @Init; @Datatypes; @bool]) in
  let bool := match bool with
  | Std.IndRef ind => ind
  | _ => Control.throw Not_found
  end in
  (* scheme_find should return (or generate) the rect_dep scheme for bool *)
  let _ref := Ind.scheme_find "rect_dep" bool in
  ().
