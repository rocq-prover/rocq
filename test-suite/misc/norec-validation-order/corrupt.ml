(* Flip one byte of the MD5 checksum stored after the data of a segment of a
   .vo file. The marshalled data itself is left untouched, so that reading the
   file without validation still succeeds. See lib/objFile.ml for the format. *)

let input_int64 ch =
  let rec go i accu =
    if i = 0 then accu
    else go (i - 1) (Int64.logor (Int64.shift_left accu 8) (Int64.of_int (input_byte ch)))
  in
  go 8 0L

let () =
  let file = Sys.argv.(1) in
  let segment = Sys.argv.(2) in
  let ch = open_in_bin file in
  let () = seek_in ch 8 in
  let summary_pos = input_int64 ch in
  let () = LargeFile.seek_in ch summary_pos in
  let n = input_binary_int ch in
  let pos = ref None in
  for _ = 1 to n do
    let nlen = input_binary_int ch in
    let name = really_input_string ch nlen in
    let p = input_int64 ch in
    let len = input_int64 ch in
    let _hash = really_input_string ch 16 in
    if String.equal name segment then pos := Some (Int64.add p len)
  done;
  close_in ch;
  match !pos with
  | None -> prerr_endline ("no segment " ^ segment ^ " in " ^ file); exit 1
  | Some p ->
    let ch = open_in_bin file in
    let () = LargeFile.seek_in ch p in
    let b = input_byte ch in
    let () = close_in ch in
    let ch = open_out_gen [Open_wronly; Open_binary] 0o644 file in
    let () = LargeFile.seek_out ch p in
    let () = output_byte ch (b lxor 1) in
    close_out ch
