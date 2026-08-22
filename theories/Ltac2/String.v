(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Ltac2.Init.
Require Ltac2.Int.
Require Ltac2.Char.
Require Ltac2.Bool.
Require Ltac2.Control.

Ltac2 Type t := string.

Ltac2 @external make : int -> char -> string := "rocq-runtime.plugins.ltac2" "string_make".
Ltac2 @external length : string -> int := "rocq-runtime.plugins.ltac2" "string_length".
Ltac2 @external get : string -> int -> char := "rocq-runtime.plugins.ltac2" "string_get".
Ltac2 @external set : string -> int -> char -> unit := "rocq-runtime.plugins.ltac2" "string_set".
Ltac2 @external concat : string -> string list -> string := "rocq-runtime.plugins.ltac2" "string_concat".
Ltac2 @external app : string -> string -> string := "rocq-runtime.plugins.ltac2" "string_app".
Ltac2 @external sub : string -> int -> int -> string := "rocq-runtime.plugins.ltac2" "string_sub".
Ltac2 @external equal : string -> string -> bool := "rocq-runtime.plugins.ltac2" "string_equal".
Ltac2 @external compare : string -> string -> int := "rocq-runtime.plugins.ltac2" "string_compare".

Ltac2 is_empty s := match s with "" => true | _ => false end.

(** [starts_with prefix s] tests whether [s] begins with [prefix]. *)
Ltac2 starts_with (prefix : string) (s : string) : bool :=
  let len_pre := length prefix in
  if Int.lt (length s) len_pre then false
  else
    let rec aux i :=
      if Int.equal i len_pre then true
      else if Char.equal (get s i) (get prefix i) then aux (Int.add i 1)
      else false
    in aux 0.

(** [ends_with suffix s] tests whether [s] ends with [suffix]. *)
Ltac2 ends_with (suffix : string) (s : string) : bool :=
  let len_suf := length suffix in
  let diff := Int.sub (length s) len_suf in
  if Int.lt diff 0 then false
  else
    let rec aux i :=
      if Int.equal i len_suf then true
      else if Char.equal (get s (Int.add diff i)) (get suffix i) then aux (Int.add i 1)
      else false
    in aux 0.

(** [index_from_opt s i c] returns the position of the first occurrence
    of [c] in [s] at or after position [i], if any.  Throws an
    exception if [i] is not a valid position in [s] (i.e. not between
    [0] and [length s]). *)
Ltac2 index_from_opt (s : string) (i : int) (c : char) : int option :=
  let l := length s in
  Control.assert_valid_argument "String.index_from_opt"
    (Bool.and (Int.ge i 0) (Int.le i l));
  let rec aux i :=
    if Int.ge i l then None
    else if Char.equal (get s i) c then Some i
    else aux (Int.add i 1)
  in aux i.

(** [index_from s i c] is like [index_from_opt s i c], but throws
    [Not_found] if [c] does not occur in [s] at or after position [i]. *)
Ltac2 index_from (s : string) (i : int) (c : char) : int :=
  match index_from_opt s i c with
  | Some n => n
  | None => Control.throw Not_found
  end.

(** [index_opt s c] returns the position of the first occurrence of
    [c] in [s], if any. *)
Ltac2 index_opt (s : string) (c : char) : int option := index_from_opt s 0 c.

(** [index s c] returns the position of the first occurrence of [c] in
    [s]; throws [Not_found] if there is none. *)
Ltac2 index (s : string) (c : char) : int := index_from s 0 c.
