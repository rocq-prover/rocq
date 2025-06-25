open Names

let print_hook =
  let attr : Declare.Hook.t list Attributes.attribute =
    let hook = Declare.Hook.make @@ fun data ->
      Feedback.msg_info Pp.(str "generated " ++ GlobRef.print data.dref ++ str "\n")
    in
    let open Attributes in
    let open Attributes.Notations in
    map (Option.default []) @@ attribute_of_list [("print", fun ?loc _ _ -> [hook])]
  in
  Vernacentries.DefAttributes.Observer.register ~name:"print-afterwards" attr


let error_hook =
  let attr : Declare.Hook.t list Attributes.attribute =
    let hook loc = Declare.Hook.make @@ fun data ->
      Feedback.msg_info Pp.(str "failing attribute") ;
      CErrors.user_err ?loc Pp.(str "attribute error!")
    in
    let open Attributes in
    let open Attributes.Notations in
    map (Option.default []) @@ attribute_of_list [("error", fun ?loc _ _ -> [hook loc])]
  in
  Vernacentries.DefAttributes.Observer.register ~name:"error" attr

let () =
  Mltop.(declare_cache_obj_full @@ interp_only_obj @@ fun () ->
         Vernacentries.DefAttributes.Observer.activate print_hook;
         Vernacentries.DefAttributes.Observer.activate error_hook)
    "rocq-test-suite.attribute"
