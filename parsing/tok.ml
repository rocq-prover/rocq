(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** The type of token for the Rocq lexer and parser *)

let string_equal (s1 : string) s2 = s1 = s2

type 'c p =
  | PKEYWORD : string -> string p
  | PIDENT : string option -> string p
  | PFIELD : string option -> string p
  | PNUMBER : NumTok.Unsigned.t option -> NumTok.Unsigned.t p
  | PSTRING : string option -> string p
  | PLEFTQMARK : unit p
  | PBULLET : string option -> string p
  | PQUOTATION : string -> string p
  | PEOI : unit p

let pattern_exact : type c. c p -> bool = function
  | PKEYWORD _ -> true
  | PIDENT id -> Option.has_some id
  | PFIELD s -> Option.has_some s
  | PNUMBER n -> Option.has_some n
  | PSTRING s -> Option.has_some s
  | PLEFTQMARK -> false
  | PBULLET s -> Option.has_some s
  | PQUOTATION _ -> true
  | PEOI -> false

type t =
  | KEYWORD of string
  | IDENT of string
  | FIELD of string
  | NUMBER of NumTok.Unsigned.t
  | STRING of string
  | LEFTQMARK
  | BULLET of string
  | QUOTATION of string * string
  | EOI

let equal_p (type a b) (t1 : a p) (t2 : b p) : (a, b) Util.eq option =
  let streq s1 s2 = match s1, s2 with None, None -> true
    | Some s1, Some s2 -> string_equal s1 s2 | _ -> false in
  match t1, t2 with
  | PIDENT s1, PIDENT s2 when streq s1 s2 -> Some Util.Refl
  | PKEYWORD s1, PKEYWORD s2 when string_equal s1 s2 -> Some Util.Refl
  | PIDENT (Some s1), PKEYWORD s2 when string_equal s1 s2 -> Some Util.Refl
  | PKEYWORD s1, PIDENT (Some s2) when string_equal s1 s2 -> Some Util.Refl
  | PFIELD s1, PFIELD s2 when streq s1 s2 -> Some Util.Refl
  | PNUMBER None, PNUMBER None -> Some Util.Refl
  | PNUMBER (Some n1), PNUMBER (Some n2) when NumTok.Unsigned.equal n1 n2 -> Some Util.Refl
  | PSTRING s1, PSTRING s2 when streq s1 s2 -> Some Util.Refl
  | PLEFTQMARK, PLEFTQMARK -> Some Util.Refl
  | PBULLET s1, PBULLET s2 when streq s1 s2 -> Some Util.Refl
  | PQUOTATION s1, PQUOTATION s2 when string_equal s1 s2 -> Some Util.Refl
  | PEOI, PEOI -> Some Util.Refl
  | _ -> None

let equal a b = match a, b with
  | KEYWORD a, KEYWORD b -> String.equal a b
  | IDENT a, IDENT b -> String.equal a b
  | FIELD a, FIELD b -> String.equal a b
  | NUMBER a, NUMBER b -> NumTok.Unsigned.equal a b
  | STRING a, STRING b -> String.equal a b
  | LEFTQMARK, LEFTQMARK -> true
  | BULLET a, BULLET b -> String.equal a b
  | QUOTATION (a1,a2), QUOTATION (b1,b2) -> String.equal a1 b1 && String.equal a2 b2
  | EOI, EOI -> true
  | (KEYWORD _ | IDENT _ | FIELD _ | NUMBER _ | STRING _
    | LEFTQMARK | BULLET _ | QUOTATION _ | EOI), _ ->
    false

let pattern_text : type c. c p -> string = function
  | PKEYWORD t -> "'" ^ t ^ "'"
  | PIDENT None -> "identifier"
  | PIDENT (Some t) -> "'" ^ t ^ "'"
  | PNUMBER None -> "number"
  | PNUMBER (Some n) -> "'" ^ NumTok.Unsigned.sprint n ^ "'"
  | PSTRING None -> "string"
  | PSTRING (Some s) -> "STRING \"" ^ s ^ "\""
  | PLEFTQMARK -> "LEFTQMARK"
  | PEOI -> "end of input"
  | PFIELD None -> "FIELD"
  | PFIELD (Some s) -> "FIELD \"" ^ s ^ "\""
  | PBULLET None -> "BULLET"
  | PBULLET (Some s) -> "BULLET \"" ^ s ^ "\""
  | PQUOTATION lbl -> "QUOTATION \"" ^ lbl ^ "\""

let extract_string diff_mode = function
  | KEYWORD s -> s
  | IDENT s -> s
  | STRING s ->
    if diff_mode then
      let escape_quotes s =
        let len = String.length s in
        let buf = Buffer.create len in
        for i = 0 to len-1 do
          let ch = String.get s i in
          Buffer.add_char buf ch;
          if ch = '"' then Buffer.add_char buf '"' else ()
        done;
        Buffer.contents buf
      in
      "\"" ^ (escape_quotes s) ^ "\""
    else s
  | FIELD s -> if diff_mode then "." ^ s else s
  | NUMBER n -> NumTok.Unsigned.sprint n
  | LEFTQMARK -> "?"
  | BULLET s -> s
  | QUOTATION(_,s) -> s
  | EOI -> ""

(* Invariant, txt is "ident" or a well parenthesized "{{....}}" *)
let trim_quotation txt =
  let len = String.length txt in
  if len = 0 then None, txt
  else
    let c = txt.[0] in
    if c = '(' || c = '[' || c = '{' then
      let rec aux n =
        if n < len && txt.[n] = c then aux (n+1)
        else Some c, String.sub txt n (len - (2*n))
      in
        aux 0
    else None, txt

let match_pattern (type c) (p : c p) : t -> c option =
  let seq = string_equal in
  match p with
  | PKEYWORD s ->
    (function KEYWORD s' when seq s s' -> Some s'
            | NUMBER n when seq s (NumTok.Unsigned.sprint n) -> Some s
            | STRING s' when seq s (CString.quote_coq_string s') -> Some s
            | _ -> None)
  | PIDENT None -> (function IDENT s' -> Some s' | _ -> None)
  | PIDENT (Some s) -> (function (IDENT s' | KEYWORD s') when seq s s' -> Some s' | _ -> None)
  | PFIELD None -> (function FIELD s -> Some s| _ -> None)
  | PFIELD (Some s) -> (function FIELD s' when seq s s' -> Some s' | _ -> None)
  | PNUMBER None -> (function NUMBER s -> Some s| _ -> None)
  | PNUMBER (Some n) ->
    let s = NumTok.Unsigned.sprint n in
    (function NUMBER n' when s = NumTok.Unsigned.sprint n' -> Some n' | _ -> None)
  | PSTRING None -> (function STRING s -> Some s | _ -> None)
  | PSTRING (Some s) -> (function STRING s' when seq s s' -> Some s' | _ -> None)
  | PLEFTQMARK -> (function LEFTQMARK -> Some () | _ -> None)
  | PBULLET None -> (function BULLET s -> Some s | _ -> None)
  | PBULLET (Some s) -> (function BULLET s' when seq s s' -> Some s' | _ -> None)
  | PQUOTATION lbl -> (function QUOTATION(lbl',s') when string_equal lbl lbl' -> Some s' | _ -> None)
  | PEOI -> (function EOI -> Some () | _ -> None)
