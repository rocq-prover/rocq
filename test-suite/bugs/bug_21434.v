Module Type Alphs.
End Alphs.

Module Symbol(Import A:Alphs).

  Inductive symbol :=.

End Symbol.

Module Type Grammar_T.
  Include Symbol.
End Grammar_T.

Module Type Automaton_T.
  Declare Module Gram:Grammar_T.
End Automaton_T.

Module Validator_safe(Import A:Automaton_T).

Definition head_symbs_of_state := A.Gram.symbol.

End Validator_safe.

Module Gram.

Include Symbol.

End Gram.

Module Aut.

Module Gram := Gram.

End Aut.

Module Boom := Validator_safe Aut.
