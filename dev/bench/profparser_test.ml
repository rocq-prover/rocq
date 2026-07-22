(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Benchlib
open BenchUtil

let profile =
  {|{ "traceEvents": [
{ "name": "command", "ph": "B", "ts": 100, "pid": 1, "tid": 1,
  "args": { "cmd": "Chars 0 - 1 First", "line": "1" } },
{ "name": "command", "ph": "E", "ts": 110, "pid": 1, "tid": 1,
  "args": {
    "major_words": "0 w", "minor_words": "0 w",
    "major_collect": 1, "minor_collect": 2, "heap_words": 100,
    "gc_boundaries": {
      "major_collect_start": 10, "minor_collect_start": 100,
      "major_collect_stop": 11, "minor_collect_stop": 102
    }
  } },
{ "name": "command", "ph": "B", "ts": 120, "pid": 1, "tid": 1,
  "args": { "cmd": "Chars 2 - 3 Second", "line": "2" } },
{ "name": "command", "ph": "E", "ts": 130, "pid": 1, "tid": 1,
  "args": {
    "major_words": "0 w", "minor_words": "0 w",
    "major_collect": 0, "minor_collect": 1, "heap_words": 100,
    "gc_boundaries": {
      "major_collect_start": 12, "minor_collect_start": 105,
      "major_collect_stop": 12, "minor_collect_stop": 106
    }
  } }
], "displayTimeUnit": "us" }
|}

let with_profile f =
  let file = Filename.temp_file "profparser" ".json" in
  let ch = open_out_bin file in
  output_string ch profile;
  close_out ch;
  Fun.protect ~finally:(fun () -> Sys.remove file) (fun () -> f file)

let expect_collections ~major ~minor = function
  | Some collections ->
    assert (collections.major = major);
    assert (collections.minor = minor)
  | None -> assert false

let () = with_profile @@ fun file ->
  match Profparser.parse ~file with
  | [(_, first); (_, second)] ->
    assert (first.gc_before = None);
    expect_collections ~major:1 ~minor:3 first.gc_after;
    expect_collections ~major:1 ~minor:3 second.gc_before;
    assert (second.gc_after = None)
  | _ -> assert false
