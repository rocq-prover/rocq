Local Open Scope list_scope.

Definition combine :=
fun A B : Type =>
fix combine (l : list A) (l' : list B) {struct l} : list (A * B) :=
  match l with
  | nil => nil
  | x :: tl => match l' with
               | nil => nil
               | y :: tl' => (x, y) :: combine tl tl'
               end
  end.

Fail Check (forall A B xs ys,
          @combine A B xs ys
          = (@list_rect
               _ _
               nil
               (fun x xs combine_xs ys
                => match ys with
                   | nil => nil
                   | y :: ys => (x, y) :: combine_xs ys
                   end)
               xs
               ys)).
(* Error: Anomaly "File "pretyping/cases.ml", line 1694, characters 27-33: Assertion failed."
Please report at http://coq.inria.fr/bugs/. *)
