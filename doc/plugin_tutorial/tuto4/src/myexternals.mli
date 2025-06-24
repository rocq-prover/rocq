open Ltac2_plugin
open Tac2ffi

(** We don't need to expose any APIs for the plugin to work, but we
    may if we want to allow further plugins to build on this one. *)

type custom2

val custom2 : custom2 repr
