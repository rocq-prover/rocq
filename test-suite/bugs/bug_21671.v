(* this tests a backwards compat hack, remove when the hack is removed *)

Declare Scope category_theory_scope.

Fail #[warning="+at-level-200-changed"]
Notation "'exists' x .. y , p" := (sigT (fun x => .. (sigT (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'exists'  '/  ' x  ..  y ,  '/  ' p ']'") :
  category_theory_scope.

Notation "'exists' x .. y , p" := (sigT (fun x => .. (sigT (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'exists'  '/  ' x  ..  y ,  '/  ' p ']'") :
  category_theory_scope.

Notation "'mif' b 'then' t 'else' u" :=
  (b * (t + u))
    (at level 200) : category_theory_scope.

Notation "'mif' b 'then' t 'else' u" :=
  (b * (t + u))
    (at level 200) : tactic_scope.
