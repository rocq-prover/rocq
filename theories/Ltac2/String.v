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

(** [length_common_prefix s1 s2] returns the length of the longest
    common prefix of [s1] and [s2]. *)
Ltac2 length_common_prefix (s1 : string) (s2 : string) : int :=
  let l1 := length s1 in
  let l2 := length s2 in
  let rec aux i :=
    if Int.lt i l1
    then if Int.lt i l2
         then (if Char.equal (get s1 i) (get s2 i) then aux (Int.add i 1) else i)
         else i
    else i
  in aux 0.

(** [common_prefix s1 s2] returns the longest common prefix of [s1]
    and [s2]. *)
Ltac2 common_prefix (s1 : string) (s2 : string) : string :=
  sub s1 0 (length_common_prefix s1 s2).

(** [strip_prefix prefix s] removes [prefix] from the beginning of
    [s], or returns [None] if [s] does not start with [prefix]. *)
Ltac2 strip_prefix (prefix : string) (s : string) : string option :=
  let lp := length prefix in
  if Int.equal (length_common_prefix prefix s) lp
  then Some (sub s lp (Int.sub (length s) lp))
  else None.

(** [replace_char c rep s] replaces every occurrence of the character
    [c] in [s] with the string [rep]. *)
Ltac2 replace_char (c : char) (rep : string) (s : string) : string :=
  let l := length s in
  let rec aux from i :=
    if Int.ge i l then [sub s from (Int.sub i from)]
    else if Char.equal (get s i) c
    then sub s from (Int.sub i from) :: rep :: aux (Int.add i 1) (Int.add i 1)
    else aux from (Int.add i 1)
  in concat "" (aux 0 0).
