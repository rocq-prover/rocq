
type outfiles
val delete_temps : outfiles -> unit 

type options = [`Verbose | `Shared | `ForPack of string | `Include of string | `Package of string | `Dontlink of string | `Linkpkg | `Debug | `Rectypes | `Thread | `Optimize | `Bytecode] list

val compile_module :
  ?options:options ->
  filename:string ->
  Malfunction_parser.moduleexp ->
  outfiles

val compile_cmx : ?options:options -> string -> outfiles
val compile_cmo : ?options:options -> string -> outfiles

val link_executable : ?options:options -> string -> outfiles -> int

val compile_and_load : ?options:options -> Malfunction.t -> Obj.t
