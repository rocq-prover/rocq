Goal Prop.
Proof.
  refine ?[x];shelve.
  [x]: refine _.
  Fail exact True.
  (* No more goals, but there are non-instantiated existential variables:
     Existential 1 = ?Goal : [ |- Prop]
     You can use Unshelve. *)
  Unshelve.
  (* still no goals *)
  exact True. (* fails no such goal *)
Qed. (* fails some evars remain *)
