Module Br.
  Set Universe Polymorphism.
  Inductive Box@{s;u} (A : Type@{s;u}) : Type@{s;u} := box : A -> Box A.
  Axiom wrap : forall (x : nat), Box nat.
  Section Bug.
    Variable x : nat.
    Lemma vmbug : (match wrap x with box _ v => v end) = (match wrap x with box _ v => v end).
    Proof.
      vm_compute.
      reflexivity.
    Defined.
    (* Error: Undeclared quality: β0 (maybe a bugged tactic). *)

    Lemma nativebug : (match wrap x with box _ v => v end) = (match wrap x with box _ v => v end).
    Proof.
      native_compute.
      reflexivity.
    Defined.
    (* Error: Undeclared quality: β0 (maybe a bugged tactic). *)
  End Bug.
End Br.

Module Index.
  (* checks that relevances in indices and "as" for the return predicate are correctly substituted
     (was not broken in the past AFAIK) *)
  Polymorphic Inductive sTrue@{s;} : Type@{s;Set} := sI.
  Polymorphic Inductive sFalse@{s;} : sTrue@{s;} -> Type@{s;Set} := .
  Inductive seq {A:SProp} (a:A) : A -> Prop := srefl : seq a a.

  Lemma vmfoo (x:sFalse sI) : match x return seq x x with  end = srefl _.
  Proof.
    vm_compute.
    destruct x.
  Defined.
  Lemma nativefoo (x:sFalse sI) : match x return seq x x with  end = srefl _.
  Proof.
    native_compute.
    destruct x.
  Defined.
End Index.
