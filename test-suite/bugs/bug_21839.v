Fail Definition oops : False :=
  (fix rec (x : unit) : False :=
  let f (b : False) := match b return False with end in
  let g x := x in
  rec ((ltac:(fix rec' 1; exact g) :> unit -> unit) x)) tt.
