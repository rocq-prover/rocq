
From Corelib Require Extraction.
Declare ML Module "rocq-runtime.plugins.funind".

Open Scope list_scope.

Notation "[ ]" := nil (format "[ ]") : list_scope.
Notation "[ x ]" := (cons x nil) : list_scope.
Notation "[ x ; y ; .. ; z ]" :=  (cons x (cons y .. (cons z nil) ..))
  (format "[ '[' x ;  '/' y ;  '/' .. ;  '/' z ']' ]") : list_scope.

Set Warnings "+funind".

Function foo (x:nat) :=
  match x with
  | 0 => Some []
  | S _ => Some [0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0]
  end.
(* error cannot define graph for foo *)

Check R_foo_correct.
