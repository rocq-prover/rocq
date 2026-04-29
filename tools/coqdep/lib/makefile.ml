(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Makefile's escaping rules are awful: $ is escaped by doubling and
   other special characters are escaped by backslash prefixing while
   backslashes themselves must be escaped only if part of a sequence
   followed by a special character (i.e. in case of ambiguity with a
   use of it as escaping character).  Moreover (even if not crucial)
   it is apparently not possible to directly escape ';' and leading '\t'. *)

let escape =
  let s' = Buffer.create 10 in
  fun s ->
    Buffer.clear s';
    for i = 0 to String.length s - 1 do
      let c = s.[i] in
      if c = ' ' || c = '#' || c = ':' (* separators and comments *)
        || c = '%' (* pattern *)
        || c = '?' || c = '[' || c = ']' || c = '*' (* expansion in filenames *)
        || i=0 && c = '~' && (String.length s = 1 || s.[1] = '/' ||
            'A' <= s.[1] && s.[1] <= 'Z' ||
            'a' <= s.[1] && s.[1] <= 'z') (* homedir expansion *)
      then begin
        let j = ref (i-1) in
        while !j >= 0 && s.[!j] = '\\' do
          Buffer.add_char s' '\\'; decr j (* escape all preceding '\' *)
        done;
        Buffer.add_char s' '\\';
      end;
      if c = '$' then Buffer.add_char s' '$';
      Buffer.add_char s' c
    done;
    Buffer.contents s'

open Format

type dynlink = Opt | Byte | Both | No | Variable
let option_dynlink = ref Both

let set_dyndep = function
  | "no" -> option_dynlink := No
  | "opt" -> option_dynlink := Opt
  | "byte" -> option_dynlink := Byte
  | "both" -> option_dynlink := Both
  | "var" -> option_dynlink := Variable
  | o -> CErrors.user_err Pp.(str "Incorrect -dyndep option: " ++ str o)

type pp = { pp : formatter -> unit }

let pp_of_string s = { pp = fun fmt -> pp_print_string fmt s }

let mldep_to_make base =
  match !option_dynlink with
  | No -> []
  | Byte -> [pp_of_string @@ sprintf "%s.cma" base]
  | Opt -> [pp_of_string @@ sprintf "%s.cmxs" base]
  | Both ->
    [pp_of_string @@ sprintf "%s.cma" base; pp_of_string @@ sprintf "%s.cmxs" base]
  | Variable ->
    [pp_of_string @@ sprintf "%s%s" base "$(DYNLIB)"]

let string_of_dep ~suffix = let open Dep_info.Dep in
  function
  | Require basename -> List.to_seq [{ pp = fun fmt -> fprintf fmt "%s%s" (escape basename) suffix }]
  | Ml base -> List.to_seq @@ mldep_to_make (escape base)
  | Other s -> List.to_seq @@ [pp_of_string @@ escape s]

let pp_concat pp fmt s = match Seq.uncons s with
| None -> ()
| Some (hd, s) ->
  let () = pp fmt hd in
  Seq.iter (fun data -> fprintf fmt " %a" pp data) s

let pp_dependency_list ~suffix fmt deps =
  let deps = List.to_seq deps in
  let deps = Seq.concat_map (fun dep -> string_of_dep ~suffix dep) deps in
  pp_concat (fun fmt s -> s.pp fmt) fmt deps

let option_noglob = ref false
let option_write_vos = ref false
let set_noglob glob = option_noglob := glob
let set_write_vos vos = option_write_vos := vos

let print_dep fmt { Dep_info.name; deps } =
  let ename = escape name in
    let glob = if !option_noglob then "" else ename^".glob " in
  fprintf fmt "%s.vo %s%s.v.beautified %s.required_vo: %s.v %a\n" ename glob ename ename ename
    (pp_dependency_list ~suffix:".vo") deps;
  if !option_write_vos then
    fprintf fmt "%s.vos %s.vok %s.required_vos: %s.v %a\n" ename ename ename ename
      (pp_dependency_list ~suffix:".vos") deps;
  fprintf fmt "%!"
