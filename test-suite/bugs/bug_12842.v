Ltac t := let H := lazymatch goal with H : _ |- _ => H end in
          let H' := constr:(fun x => H x) in specialize H'.

Goal (True -> True) -> True.
Proof.
  intro H.
  Info 1 t.
Abort.

Goal (True -> True) -> True /\ True.
Proof.
  intro H.
  Info 1 (split; t).
Abort.
