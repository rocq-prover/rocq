{
exception SyntaxError of (Lexing.position * Lexing.position) * string
type sexp =
  (Lexing.position * Lexing.position) * rawsexp
and rawsexp =
| Atom of string
| Var of string
| String of string
| List of sexp list

let loc lexbuf f =
  let open Lexing in
  let start = lexbuf.lex_start_p in
  let r = f () in
  ((start, lexbuf.lex_curr_p), r)

let fail lexbuf s = raise (SyntaxError ((lexbuf.Lexing.lex_start_p, lexbuf.Lexing.lex_curr_p), s))

let var s =
  assert (s.[0] = '$');
  Var (String.sub s 1 (String.length s - 1))

let rec print ppf (_, s) = let open Format in match s with
  | Atom s -> fprintf ppf "%s" s
  | Var s -> fprintf ppf "$%s" s
  | String s -> fprintf ppf "%S" s
  | List l ->
     fprintf ppf "@[<2>(%a)@]" (pp_print_list ~pp_sep:pp_print_space print) l
}

let space = [' ' '\t' '\r']*

let symbol = ['.' '&' '|' '+' '/' '-' '!' '@' '#' '%' '^' '*' '~' '?' '{' '}' '<' '>' '=']

let atomsymbol = ['+' '-' '<' '>']
let letter = ['a'-'z' 'A'-'Z' '_']
let digit = ['0' - '9']

let atom = (letter | digit | symbol)*
let var = (['a'-'z' 'A'-'Z' '_' '0'-'9' '$' '\''] | symbol)+

let string = '"' ([^ '\\' '"']* | ('\\' _))* '"'

let comment = ';' [^ '\n']*

(* FIXME: exceptions in int and str cases *)
rule sexps acc = parse
| ')'
  { List.rev acc }
| '('
  { sexps (loc lexbuf (fun () -> List (sexps [] lexbuf)) :: acc) lexbuf }
| string
  { sexps (loc lexbuf (fun () -> String (Scanf.sscanf (Lexing.lexeme lexbuf) "%S%!" (fun x -> x))) :: acc) lexbuf }
| '$' var
  { sexps (loc lexbuf (fun () -> var (Lexing.lexeme lexbuf)) :: acc) lexbuf }
| atom
  { sexps (loc lexbuf (fun () -> Atom (Lexing.lexeme lexbuf)) :: acc) lexbuf }
| '\n'
  { Lexing.new_line lexbuf; sexps acc lexbuf }
| comment
  { sexps acc lexbuf }
| space
  { sexps acc lexbuf }
| eof
  { fail lexbuf "Unexpected end of file" }
| _
  { fail lexbuf ("Lexical error on " ^ (Lexing.lexeme lexbuf)) }

and read_next_sexp = parse
| '\n'
  { Lexing.new_line lexbuf; read_next_sexp lexbuf }
| comment
  { read_next_sexp lexbuf }
| space
  { read_next_sexp lexbuf }
| '('
  { loc lexbuf (fun () -> List (sexps [] lexbuf)) }
| atom
  { loc lexbuf (fun () -> Atom (Lexing.lexeme lexbuf)) }
| eof
  { raise End_of_file }
| _
  { fail lexbuf "Sexp must start with '('" }

{

let read_only_sexp lexbuf =
  let s = read_next_sexp lexbuf in
  match read_next_sexp lexbuf with
  | _ -> fail lexbuf "File must contain only one sexp"
  | exception End_of_file -> s

}
