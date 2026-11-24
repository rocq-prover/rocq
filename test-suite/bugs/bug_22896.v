Module M.
  Sort foo.

  Constraint foo -> Prop.

  Inductive Ind : Univ@{foo;_} := C (_ : True).
End M.
