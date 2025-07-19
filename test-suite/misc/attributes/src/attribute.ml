open Names



let print_hook =
  let attr : (Declare.Hook.S.t -> unit) list Attributes.attribute =
    let fn (data : Declare.Hook.S.t) : unit =
      Feedback.msg_info Pp.(str "generated " ++ GlobRef.print data.dref ++ str "\n")
    in
    let open Attributes in
    let open Attributes.Notations in
    map (Option.default []) @@ attribute_of_list [("print", fun ?loc _ _ -> [fn])]
  in
  Vernacentries.DefAttributes.Observer.register ~name:"print-afterwards" attr


let error_hook =
  let attr : (Declare.Hook.S.t -> unit) list Attributes.attribute =
    let fn ?loc (data : Declare.Hook.S.t) : unit =
      Feedback.msg_info Pp.(str "failing attribute") ;
      CErrors.user_err ?loc Pp.(str "attribute error!")
    in
    let open Attributes in
    let open Attributes.Notations in
    map (Option.default []) @@ attribute_of_list [("error", fun ?loc _ _ -> [fn ?loc])]
  in
  Vernacentries.DefAttributes.Observer.register ~name:"error" attr

let () =
  Mltop.add_init_function "rocq-test-suite.attribute" (fun () ->
      Vernacentries.DefAttributes.Observer.activate print_hook;
      Vernacentries.DefAttributes.Observer.activate error_hook
    )
