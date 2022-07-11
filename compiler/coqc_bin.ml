let () =
  let args = List.tl (Array.to_list Sys.argv) in
  Simple_compiler.Scoqc.main args
