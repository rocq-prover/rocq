- **Changed:**
  Until 8.19 term level 200 contained a sub-entry `binder_constr`
  (containing e.g. `forall`) and notations declared at level 200 were
  redirected to `binder_constr`. In 8.19 `binder_constr` was moved to
  level 10, keeping the redirection for notations declared at level 200.

  `binder_constr` has now been removed with its parsing rules put
  directly at level 10, and notations declared at level 200 are
  redirected to level 10. Any right recursion in such a redirected
  notation is still interpreted as though it was really in right
  associative level 200, i.e. the right recursion is at level 200.

  The redirection will be removed in the future and is therefore
  deprecated. To keep the current behaviour, declare your notations at
  level 10 and any recursion at level 200. For instance,

  .. rocqdoc::

     Reserved Notation "'exists' x .. y , p"
       (at level 200, x binder).

  becomes

  .. rocqdoc::

     Reserved Notation "'exists' x .. y , p"
       (at level 10, x binder, p at level 200).

  Finally note that any `associativity` annotation on notations
  declared at level 200 are currrently ignored to avoid interfering
  with the redirection to left-associative level 10 (`#21671
  <https://github.com/rocq-prover/rocq/pull/21671>`_, by Gaëtan
  Gilbert).
