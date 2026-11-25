Ltac foo := match goal with H := context[nat] |- _ => idtac end.
Print Ltac foo.

Ltac bar := match goal with
  | H := nat |- _ => idtac
  | H := [context [nat]] : nat |- _ => idtac
  | H := [nat] : context C [Set] |- _ => idtac
  end.
Print Ltac bar.

Ltac foo' := match goal with
            | H:=[ context [ nat ] ]:_ |- _ => idtac
            end.

Ltac bar' :=
  match goal with
  | H:=nat:_ |- _ => idtac
  | H:=[ context [ nat ] ]:nat |- _ => idtac
  | H:=[ nat ]:context C[ Set ] |- _ => idtac
  end.
