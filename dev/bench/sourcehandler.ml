(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open BenchUtil

let source_substring source start stop =
  (* substring from start to stop exclusive, both 0-based *)
  String.sub source start (stop - start)

let count_newlines s = String.fold_left (fun n c -> if c = '\n' then n+1 else n) 0 s

let is_blank_char = function ' '|'\n'|'\t' -> true | _ -> false

let rec find_gap_end source start stop =
  if start <> stop && source.[stop-1] = ' ' then find_gap_end source start (stop-1)
  else stop

let rec join_loop ~source ~last_end ~lines acc = function
  | [] ->
    let sourcelen = String.length source in
    let acc = if last_end < sourcelen then
        let text = source_substring source last_end sourcelen in
        if String.for_all is_blank_char text then acc
        else
          ({ chars = { start_char = last_end; stop_char = sourcelen; };
             line = lines; text}, None)
          :: acc
      else
        acc
    in
    List.rev acc
  | (loc,v) :: rest ->
    (* loc.start_char and loc.stop_char are the 0-based character positions of
       the command: loc.start_char points at its first character and
       loc.stop_char is one past its last character. [source_substring] also
       takes 0-based positions, so the command text spans the 0-based
       characters [loc.start_char, loc.stop_char). *)
    let acc, lines, start_char =
      let start_char = find_gap_end source last_end loc.start_char in
      if start_char > last_end then
        let text = source_substring source last_end start_char in
        let n = count_newlines text in
        let acc =
          ({ chars = { start_char = last_end; stop_char = start_char; };
             line = lines; text }, None)
          :: acc
        in
        acc, (lines+n), start_char
      else acc, lines, start_char
    in
    (* absorb 1 blank after a command *)
    let stop_char =
      if loc.stop_char < String.length source &&
         is_blank_char source.[loc.stop_char] then
        loc.stop_char + 1
      else loc.stop_char in
    let text = source_substring source start_char stop_char in
    let n = count_newlines text in
    let acc =
      ({ chars = { start_char; stop_char; };
         line = lines; text }, Some v)
      :: acc
    in
    join_loop ~source ~last_end:stop_char ~lines:(lines + n) acc rest

let join_to_source ~dummy ~source vals =
  let res = join_loop ~source ~last_end:0 ~lines:1 [] vals in
  List.map (fun (loc,v) -> loc, Option.default dummy v) res
