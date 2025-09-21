.. _nsatz_chapter:

Nsatz: a solver for equalities in integral domains
===========================================================

:Author: Loïc Pottier, Laurent Thery and Lionel Blatter

.. note::
   The tactics described in this chapter require the Stdlib library.

To use the tactics described in this section, load the ``Nsatz`` module with the
command ``Require Import Nsatz``.  Alternatively, if you prefer not to transitively depend on the
files that declare the axioms used to define the real numbers, you can
``Require Import NsatzTactic`` instead; this will still allow
:tacn:`nsatz` to solve goals defined about :math:`\mathbb{Z}`,
:math:`\mathbb{Q}` and any user-registered rings.


.. tacn:: nsatz {? with radicalmax := @one_term strategy := @one_term parameters := @one_term variables := @one_term }

   This tactic is for solving goals of the form

   :math:`\begin{array}{l}
   \forall X_1, \ldots, X_n \in A, \\
   P_1(X_1, \ldots, X_n) = Q_1(X_1, \ldots, X_n), \ldots, P_s(X_1, \ldots, X_n) = Q_s(X_1, \ldots, X_n) \\
   \vdash P(X_1, \ldots, X_n) = Q(X_1, \ldots, X_n) \\
   \end{array}`

   where :math:`P, Q, P_1, Q_1, \ldots, P_s, Q_s` are polynomials and :math:`A` is an integral
   domain, i.e. a commutative ring with no zero divisors. For example, :math:`A`
   can be :math:`\mathbb{R}`, :math:`\mathbb{Z}`, or :math:`\mathbb{Q}`.
   Note that the equality :math:`=` used in these goals can be
   any setoid equality (see :ref:`tactics-enabled-on-user-provided-relations`) , not only Leibniz equality.

   It also proves formulas

   :math:`\begin{array}{l}
   \forall X_1, \ldots, X_n \in A, \\
   P_1(X_1, \ldots, X_n) = Q_1(X_1, \ldots, X_n) \wedge \ldots \wedge P_s(X_1, \ldots, X_n) = Q_s(X_1, \ldots, X_n) \\
   \rightarrow P(X_1, \ldots, X_n) = Q(X_1, \ldots, X_n) \\
   \end{array}`

   doing automatic introductions.

   `radicalmax`
     bound when searching for r such that
     :math:`c (P−Q)^r = \sum_{i=1..s} S_i (P_i − Q_i)`.
     This argument must be of type `N` (natural numbers).

   `strategy`
     gives the order on variables :math:`X_1,\ldots,X_n` and the strategy
     used in Buchberger algorithm (see :cite:`sugar` for details):

       * `strategy := 0%Z`: reverse lexicographic order and newest s-polynomial.
       * `strategy := 1%Z`: reverse lexicographic order and sugar strategy.
       * `strategy := 2%Z`: pure lexicographic order and newest s-polynomial.
       * `strategy := 3%Z`: pure lexicographic order and sugar strategy.

   `parameters`
     a list of parameters of type `R`, containing the variables :math:`X_{i_1},\ldots,X_{i_k}` among
     :math:`X_1,\ldots,X_n`.  Computation will be performed with
     rational fractions in these parameters, i.e. polynomials have
     coefficients in :math:`R(X_{i_1},\ldots,X_{i_k})`. In this case, the coefficient
     :math:`c` can be a nonconstant polynomial in :math:`X_{i_1},\ldots,X_{i_k}`, and the tactic
     produces a goal which states that :math:`c` is not zero.

   `variables`
     a list of variables of type `R` in the decreasing order in
     which they will be used in the Buchberger algorithm. If the list is empty,
     then `lvar` is replaced by all the variables which are not in
     `parameters`.

   See the file `Nsatz.v <https://github.com/rocq-prover/stdlib/blob/master/test-suite/success/Nsatz.v>`_
   for examples, especially in geometry.

.. tacn:: ensatz {? with strategy := @one_term }

   This tactic is for solving goals of the form

   :math:`\begin{array}{l}
   \forall X_1, \ldots, X_n \in A, \\
   P_1(X_1, \ldots, X_n) = Q_1(X_1, \ldots, X_n), \ldots, P_s(X_1, \ldots, X_n) = Q_s(X_1, \ldots, X_n) \\
   \vdash \exists Y_1, \ldots, Y_m \in A, \\
   P(X_1, \ldots, X_n) = Y_1 * Q_1'(X_1, \ldots, X_n) + \ldots + Y_m * Q_m'(X_1, \ldots, X_n)
   \end{array}`

   where :math:`P, P_1, Q_1, Q_1', , \ldots, P_s, Q_s, Q_m'` are polynomials and :math:`A` is an integral
   domain, i.e. a commutative ring with no zero divisors. For example, :math:`A`
   can be :math:`\mathbb{R}`, :math:`\mathbb{Z}`, or :math:`\mathbb{Q}`.
   Note that the equality :math:`=` used in these goals can be
   any setoid equality (see :ref:`tactics-enabled-on-user-provided-relations`) , not only Leibniz equality.

   It also proves formulas

   :math:`\begin{array}{l}
   \forall X_1, \ldots, X_n \in A, \\
   P_1(X_1, \ldots, X_n) = Q_1(X_1, \ldots, X_n) \wedge \ldots \wedge P_s(X_1, \ldots, X_n) = Q_s(X_1, \ldots, X_n) \\
   \rightarrow \exists Y_1, \ldots, Y_m \in A,\\
   P(X_1, \ldots, X_n) = Y_1 * Q_1'(X_1, \ldots, X_n) + \ldots + Y_m * Q_m'(X_1, \ldots, X_n)
   \end{array}`

   doing automatic introductions.

   The tactic can also solve goals with existentiel variables.

   .. example::

     .. rocqtop:: all extra-stdlib

       From Stdlib Require Import Znumtheory.
       From Stdlib Require Import ZArith.
       From Stdlib Require Import ZNsatz.

       Goal forall a b n j x y z : Z,
           a - j = x * n ->
           b - y = z * n ->
           exists k : Z, a * b - j * y = k * n.
       Proof.
         intros. eexists. ensatz.
       Qed.


   See the file
   `ENsatz.v <https://github.com/rocq-prover/stdlib/blob/master/test-suite/success/ENsatz.v>`_
   for examples.

More about `nsatz`
---------------------

Hilbert’s Nullstellensatz theorem shows how to reduce proofs of
equalities on polynomials on a commutative ring :math:`A` with no zero divisors
to algebraic computations: it is easy to see that if a polynomial :math:`P` in
:math:`A[X_1,\ldots,X_n]` verifies :math:`c P^r = \sum_{i=1}^{s} S_i P_i`, with
:math:`c \in A`, :math:`c \not = 0`,
:math:`r` a positive integer, and the :math:`S_i` s in :math:`A[X_1,\ldots,X_n ]`,
then :math:`P` is zero whenever polynomials :math:`P_1,\ldots,P_s` are zero
(the converse is also true when :math:`A` is an algebraically closed field: the method is
complete).

So, solving our initial problem reduces to finding :math:`S_1, \ldots, S_s`,
:math:`c` and :math:`r` such that :math:`c (P-Q)^r = \sum_{i} S_i (P_i-Q_i)`,
which will be proved by the tactic ring.

This is achieved by the computation of a Gröbner basis of the ideal
generated by :math:`P_1-Q_1,...,P_s-Q_s`, with an adapted version of the
Buchberger algorithm.

This computation is done after a step of *reification*, which is
performed using :ref:`typeclasses`.

.. tacn:: nsatz_compute @one_term
   :undocumented:
