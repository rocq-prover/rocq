(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module type S = module type of String

include String

let rec hash len s i accu =
  if i = len then accu
  else
    let c = Char.code (String.unsafe_get s i) in
    hash len s (succ i) (accu * 19 + c)

let hash s =
  let len = String.length s in
  hash len s 0 0

let explode s =
  let rec explode_rec n =
    if n >= String.length s then
      []
    else
      String.make 1 (String.get s n) :: explode_rec (succ n)
  in
  explode_rec 0

let implode sl = String.concat "" sl

let is_empty s = String.length s = 0

let drop_simple_quotes s =
  let n = String.length s in
  if n > 2 && s.[0] = '\'' && s.[n-1] = '\'' then String.sub s 1 (n-2) else s

let quote_coq_string s =
  let b = Buffer.create (String.length s + 2) in
  Buffer.add_char b '"';
  for i = 0 to String.length s - 1 do
    Buffer.add_char b s.[i];
    if s.[i] = '"' then Buffer.add_char b s.[i];
  done;
  Buffer.add_char b '"';
  Buffer.contents b

let unquote_coq_string s =
  let b = Buffer.create (String.length s) in
  let n = String.length s in
  if n < 2 || s.[0] <> '"' || s.[n-1] <> '"' then None else
    let i = ref 1 in
    try
      while !i < n - 1 do
        Buffer.add_char b s.[!i];
        if s.[!i] = '"' then
          if !i < n - 2 && s.[!i+1] = '"' then incr i
          else raise Exit;
        incr i
      done;
      Some (Buffer.contents b)
    with Exit -> None

let html_escape msg =
  let buf = Buffer.create (String.length msg) in
  String.iter (fun c ->
      if String.contains "\"&'<>" c then
        Buffer.add_string buf (Printf.sprintf "&#%d;" (Char.code c))
      else
        Buffer.add_char buf c)
    msg;
  Buffer.contents buf

(* substring searching... *)

(* gdzie = where, co = what *)
(* gdzie=gdzie(string) gl=gdzie(length) gi=gdzie(index) *)
let rec raw_is_sub gdzie gl gi co cl ci =
  (ci>=cl) ||
  ((String.unsafe_get gdzie gi = String.unsafe_get co ci) &&
   (raw_is_sub gdzie gl (gi+1) co cl (ci+1)))

let rec raw_str_index i gdzie l c co cl =
  (* First adapt to ocaml 3.11 new semantics of index_from *)
  if (i+cl > l) then raise Not_found;
  (* Then proceed as in ocaml < 3.11 *)
  let i' = String.index_from gdzie i c in
    if (i'+cl <= l) && (raw_is_sub gdzie l i' co cl 0) then i' else
      raw_str_index (i'+1) gdzie l c co cl

let string_index_from gdzie i co =
  if co="" then i else
    raw_str_index i gdzie (String.length gdzie)
      (String.unsafe_get co 0) co (String.length co)

let string_contains ~where ~what =
  try
    let _ = string_index_from where 0 what in true
  with
      Not_found -> false

let is_sub p s off =
  let lp = String.length p in
  let ls = String.length s in
  if ls < off + lp then false
  else
    let rec aux i =
      if lp <= i then true
      else
        let cp = String.unsafe_get p i in
        let cs = String.unsafe_get s (off + i) in
        if cp = cs then aux (succ i) else false
    in
    aux 0

let is_prefix p s =
  is_sub p s 0

let is_suffix p s =
  is_sub p s (String.length s - String.length p)

let plural n s = if n<>1 then s^"s" else s

let lplural l s =
  match l with
  | [_] -> s
  | _ -> s^"s"

let conjugate_verb_to_be n = if n<>1 then "are" else "is"

let ordinal n =
  let s =
    if (n / 10) mod 10 = 1 then "th"
    else match n mod 10 with
    | 1 -> "st"
    | 2 -> "nd"
    | 3 -> "rd"
    | _ -> "th"
  in
  string_of_int n ^ s

(* this and edit_distance copied from ocaml stdlib *)

let uchar_array_of_utf_8_string s =
  let slen = length s in (* is an upper bound on Uchar.t count *)
  let uchars = Array.make slen Uchar.max in
  let k = ref 0 and i = ref 0 in
  while (!i < slen) do
    let dec = get_utf_8_uchar s !i in
    i := !i + Uchar.utf_decode_length dec;
    uchars.(!k) <- Uchar.utf_decode_uchar dec;
    incr k;
  done;
  uchars, !k

let edit_distance ?(limit = Stdlib.Int.max_int) s0 s1 =
  if limit <= 1 then (if equal s0 s1 then 0 else limit) else
  let[@inline] minimum a b c = Stdlib.Int.min a (Stdlib.Int.min b c) in
  let s0, len0 = uchar_array_of_utf_8_string s0 in
  let s1, len1 = uchar_array_of_utf_8_string s1 in
  let limit = Stdlib.Int.min (Stdlib.Int.max len0 len1) limit in
  if Stdlib.Int.abs (len1 - len0) >= limit then limit else
  let s0, s1 = if len0 > len1 then s0, s1 else s1, s0 in
  let len0, len1 = if len0 > len1 then len0, len1 else len1, len0 in
  let rec loop row_minus2 row_minus1 row i len0 limit s0 s1 =
    if i > len0 then row_minus1.(Array.length row_minus1 - 1) else
    let len1 = Array.length row - 1 in
    let row_min = ref Stdlib.Int.max_int in
    row.(0) <- i;
    let jmax =
      let jmax = Stdlib.Int.min len1 (i + limit - 1) in
      if jmax < 0 then (* overflow *) len1 else jmax
    in
    for j = Stdlib.Int.max 1 (i - limit) to jmax do
      let cost = if Uchar.equal s0.(i-1) s1.(j-1) then 0 else 1 in
      let min = minimum
          (row_minus1.(j-1) + cost) (* substitute *)
          (row_minus1.(j) + 1)      (* delete *)
          (row.(j-1) + 1)           (* insert *)
          (* Note when j = i - limit, the latter [row] read makes a bogus read
             on the value that was in the matrix at d.(i-2).(i - limit - 1).
             Since by induction for all i,j, d.(i).(j) >= abs (i - j),
             (row.(j-1) + 1) is greater or equal to [limit] and thus does
             not affect adversely the minimum computation. *)
      in
      let min =
        if (i > 1 && j > 1 &&
            Uchar.equal s0.(i-1) s1.(j-2) &&
            Uchar.equal s0.(i-2) s1.(j-1))
        then Stdlib.Int.min min (row_minus2.(j-2) + cost) (* transpose *)
        else min
      in
      row.(j) <- min;
      row_min := Stdlib.Int.min !row_min min;
    done;
    if !row_min >= limit then (* can no longer decrease *) limit else
    loop row_minus1 row row_minus2 (i + 1) len0 limit s0 s1
  in
  let ignore =
    (* Value used to make the values around the diagonal stripe ignored
       by the min computations when we have a limit. *)
    limit + 1
  in
  let row_minus2 = Array.make (len1 + 1) ignore in
  let row_minus1 = Array.init (len1 + 1) (fun x -> x) in
  let row = Array.make (len1 + 1) ignore in
  let d = loop row_minus2 row_minus1 row 1 len0 limit s0 s1 in
  if d > limit then limit else d

(* modified from edit_distance to match a substring *)
let edit_distance_substring ?(limit = Stdlib.Int.max_int) ~pattern:s0 s1 =
  let[@inline] minimum a b c = Stdlib.Int.min a (Stdlib.Int.min b c) in
  (* XXX we should be able to cache s0
     instead recomputing every time we do the check *)
  let s0, len0 = uchar_array_of_utf_8_string s0 in
  let s1, len1 = uchar_array_of_utf_8_string s1 in
  if len0 - len1 >= limit then limit else
    let rec loop row_minus2 row_minus1 row i len0 limit s0 s1 =
      if i > len0 then Array.fold_left Stdlib.Int.min Stdlib.Int.max_int row_minus1 else
        let len1 = Array.length row - 1 in
        let row_min = ref Stdlib.Int.max_int in
        row.(0) <- i;
        (* stdlib has some limit-based shortcuts here but naively
           copying them doesn't work for substring matching *)
        for j = 1 to len1 do
          let cost = if Uchar.equal s0.(i-1) s1.(j-1) then 0 else 1 in
          let min = minimum
              (row_minus1.(j-1) + cost) (* substitute *)
              (row_minus1.(j) + 1)      (* delete *)
              (row.(j-1) + 1)           (* insert *)
          in
          let min =
            if (i > 1 && j > 1 &&
                Uchar.equal s0.(i-1) s1.(j-2) &&
                Uchar.equal s0.(i-2) s1.(j-1))
            then Stdlib.Int.min min (row_minus2.(j-2) + cost) (* transpose *)
            else min
          in
          row.(j) <- min;
          row_min := Stdlib.Int.min !row_min min;
        done;
        if !row_min >= limit then (* can no longer decrease *) limit else
          loop row_minus1 row row_minus2 (i + 1) len0 limit s0 s1
    in
    let ignore =
      (* Value used to make the values around the diagonal stripe ignored
         by the min computations when we have a limit. *)
      (* XXX why is max_int + 1 not a problem? *)
      limit + 1
    in
    let row_minus2 = Array.make (len1 + 1) ignore in
    (* for substring matching row_minus1 starts with constant 0 instead of stdlib (fun x -> x) *)
    let row_minus1 = Array.make (len1 + 1) 0 in
    let row = Array.make (len1 + 1) ignore in
    loop row_minus2 row_minus1 row 1 len0 limit s0 s1

(* string parsing *)

module Self =
struct
  type t = string
  let compare = compare
end

module Set = CSet.Make(Self)
module Map = CMap.Make(Self)
module Pred = Predicate.Make(Self)

module List = struct
  type elt = string
  let mem id l = List.exists (fun s -> equal id s) l
  let assoc id l = CList.assoc_f equal id l
  let remove_assoc id l = CList.remove_assoc_f equal id l
  let mem_assoc id l = List.exists (fun (a,_) -> equal id a) l
  let mem_assoc_sym id l = List.exists (fun (_,b) -> equal id b) l
  let equal l l' = CList.equal equal l l'
end

module Hstring = Hashcons.Make(struct
    type t = string
    let hashcons s = hash s, s
    let eq = String.equal
  end)

let hcons = Hashcons.simple_hcons Hstring.generate Hstring.hcons ()
