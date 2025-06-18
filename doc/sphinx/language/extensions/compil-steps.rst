.. _compil-steps:

========================
Command level processing
========================

When a command, for instance :g:`Check 1 + 2 * 2.` is fed to Rocq, it
goes through several *successive* processing steps:

* :term:`lexing` splits the input string into a sequence of tokens ;
* :term:`parsing` converts the sequence of tokens into a syntax tree ;
* :term:`synterp` does just enough to be able to proceed parsing the
  file (that is, executes the few commands that can modify the lexer
  or parser) ;
* :term:`interp` executes the bulk of the parsed commands.

.. note::

   Understanding the distinction between lexing and parsing is
   sometimes required to make good use of the notation features.
   The synterp/interp distinction, while important for developers,
   should be mostly transparent for users.

Lexing
~~~~~~

The first step, :gdef:`lexing` splits the input into a sequence of
tokens, for instance the string ``"Check 1 + 2 * 2."`` is split into
the sequence of seven tokens `'Check' '1' '+' '2' '*' '2' '.'`. A set
of :ref:`basic tokens <lexical-conventions>` are predefined and can be
extended, in particular by
:ref:`reserving notations <ReservingNotations>`.

Parsing
~~~~~~~

During :gdef:`parsing` the sequence of tokens is interpreted as a
tree, for instance here:

.. code-block:: text
   :name: after-parsing

         Check
           |
           +
          / \
         1   *
            / \
           2   2

The parsed grammar can be modified, for instance by
:ref:`reserving notations <ReservingNotations>`.

Synterp
~~~~~~~

In addition to the above lexing and parsing, the :gdef:`synterp` phase
does just enough to be able to parse the remaining commands.
Typically, this means applying the effects of :cmd:`Reserved Notation`
commands. Plugins loading, :cmd:`Require` and :cmd:`Import` commands
can also have synterp effects.

Interp
~~~~~~

The :gdef:`interp` phase performs the specific effect of each command.
If the command contains terms, they will be processed in distinct
steps as explained below.

.. note::

   Depending on the Rocq interface used (``rocq compile``, ``rocq
   top`` or various IDEs), Rocq may run the interp phase for each
   command immediately after its synterp phase, or it may run the
   synterp phase for every command in the file before running any
   interp step, or any other interleaving.

=====================
Term level processing
=====================

It is in theory possible to write down every term explicitly
as described in the :ref:`Core Language <core-language>` part of this
manual, for instance
:n:`Nat.add (S O) (Nat.mul (S (S O)) (S (S O)))`. However, this would
be very tedious and error-prone and takes us away from our usual
mathematical practice. To circumvent this, Rocq offers multiple
preprocessing mechanisms to help fill the gap between what the users
would like to input to the system and the fully formal core language
expected by the kernel. We give an overview of all these steps below.

For instance, the notation mechanisms reflect the eponymous mathematical
practice and allows to write :n:`1 + 2 * 2` instead of the above
term. Those mechanisms range from simple :ref:`Abbreviations` to full
fledged :ref:`Notations` with user defined :ref:`syntaxes
<ReservingNotations>`. Multiple interpretations can be given to the
same syntax in different contexts thanks to the :ref:`scope
<Scopes>` mechanism. For instance :n:`(1 + 2 * 2)%N` can be
the above natural number expression while :n:`(1 + 2 * 2)%Z` can be
an expression with integers.

In order to take the best part of all these preprocessing mechanisms,
one needs a basic understanding of the multiple steps needed to
transform an inputted term (possibly with notations) into the valid
Gallina term which Rocq will ultimately use internally. Terms given as input
to Rocq go through several successive steps:

* First, :term:`lexing`, then :term:`parsing`, are performed as part
  of any command processing, as described above.

* During :gdef:`internalization` a number of things are resolved. This
  includes :ref:`name resolution <qualified-names>`, :term:`notation
  interpretation` and introduction of :term:`holes <hole>` for :ref:`implicit
  arguments <ImplicitArguments>`.
  :gdef:`Notation interpretation <notation interpretation>`
  translates each syntactic element to a term,
  for instance :n:`1` can be interpreted as the
  natural number :n:`S O` then :n:`2` is interpreted as :n:`S (S O)`,
  then :n:`2 * 2` as :n:`Nat.mul (S (S O)) (S (S O))` and finally our
  whole term as :n:`Nat.add (S O) (Nat.mul (S (S O)) (S (S O)))`. The
  same expression can be given multiple interpretations in various
  contexts thanks to :ref:`Scopes`.

* Finally, :gdef:`type inference`, can use the various mechanisms described in
  this section to fill gaps (for instance with :ref:`canonical structures
  <canonicalstructures>` or :ref:`typeclasses`) or fix terms (for
  instance with :ref:`coercions <coercions>`) to obtain fully detailed terms in
  the :ref:`Core Language <core-language>`.

For each term, Rocq performs these steps *successively* and
*independently*.
Then, the result goes through the type checking phases discussed in
:ref:`previous chapter <core-language>`.
None of the steps has any impact on the previous ones.
In particular, no typechecking is involved during parsing or
internalization. Also note that none of the features resolved during
these phases, like unqualified names, implicit arguments or notations,
remains during the later type inference and type checking phases.

.. note::

   The :term:`type inference` phase together with, all or part of, the
   previous steps is sometimes called elaboration in the literature.

.. example:: Simple interleaving of intern and type inference phases

   The command :g:`Definition foo : T := body.` has a trivial
   :term:`synterp` phase. Indeed, it doesn't influence any further
   parsing. Its :term:`interp` phase will internalize :g:`T` and infer
   types in it, then it will internalize :g:`body` and infer types in
   it, using :g:`T` as expected type. Note that the result of type
   inference in :g:`T` matters in internalization of :g:`body`, for
   instance for selecting notation scopes. Finally, the resulting
   :g:`foo : T := body` is sent to the kernel.

.. example:: Delayed steps

   :g:`Ltac foo := exact term.` will internalize :g:`term` and save
   the result. Only when the :g:`foo` tactic will be called, will the
   type inference on the resulting :n:`term` be run, with the type of
   the current goal as expected type. If this succeeds, the proof
   state will be updated to fill the goal, and the kernel will see the
   result at :cmd:`Qed`.

.. example:: Reserved notation

   The command :g:`Reserved Notation "x + y" (at level 50, left
   associativity).` has a non trivial synterp phase, as it extends the
   parser so that :n:`_ + _` can later be parsed. Its interp phase is
   then trivial, as there is nothing left to do.
