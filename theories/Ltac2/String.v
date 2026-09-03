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

(** [split_on_char sep s] splits [s] into the (possibly empty)
    substrings delimited by occurrences of [sep], following the
    conventions of OCaml's [String.split_on_char]: the result is never
    empty, and [concat (make 1 sep) (split_on_char sep s)] is equal to
    [s]. *)
Ltac2 split_on_char (sep : char) (s : string) : string list :=
  let l := length s in
  let rec aux from i :=
    if Int.ge i l then [sub s from (Int.sub i from)]
    else if Char.equal (get s i) sep
    then sub s from (Int.sub i from) :: aux (Int.add i 1) (Int.add i 1)
    else aux from (Int.add i 1)
  in aux 0 0.

(** [trim s] removes leading and trailing whitespace
    (cf [Char.is_space]) from [s]. *)
Ltac2 trim (s : string) : string :=
  let l := length s in
  let rec up i :=
    if Int.lt i l then (if Char.is_space (get s i) then up (Int.add i 1) else i) else i in
  let rec down i :=
    let i' := Int.sub i 1 in
    if Int.ge i' 0 then (if Char.is_space (get s i') then down i' else i) else i in
  let start := up 0 in
  let stop := down l in
  if Int.le stop start then "" else sub s start (Int.sub stop start).
