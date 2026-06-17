# Syntax and semantics of Malfunction

**Note**: This "specification" is preliminary at best, and subject to
  change when bugs are found, features are added, or I'm bored.

Malfunction does only very basic checking of syntax when loading a
program. For any program which passes the syntax checker, Malfunction
should do one of the following:

  - Produce exactly the same result in the intepreter (`malfunction eval`) and compiler (`malfunction compile`)
  - Report it as having undefined behaviour in the interpreter (`malfunction eval`)
  - Fail to terminate in both the interpreter and the compiler

The behaviour of the interpreter and compiler should agree with the
text below, although for a more precise specification you should look
at the
[definition of the interpreter](../src/malfunction_interpreter.ml),
which is straightforward (no bytecode or other efficiency tricks, just
syntax-directed execution).

It's not necessarily a bug in Malfunction if a program compiles with
`malfunction compile` and then crashes at runtime. This specification
intentionally leaves much behaviour undefined, so you should count
yourself lucky if a program like `(field 0 0)` is well-behaved enough
to merely crash.

However, the interpreter should detect *all* undefined behaviour
(Malfunction's semantics are kept quite simple to ensure that this is
easy). If a program runs to completion in the intepreter producing a
result, it is a bug in Malfunction if the compiled version of the same
program either crashes or produces a different value, and
[should be reported](https://github.com/stedolan/malfunction/issues).

This doesn't apply to programs which link with OCaml code: if you use
`(global ...)` to call an OCaml function, it's up to you to ensure
that you pass inputs that won't make it crash, and the interpreter
will (currently) be of no help checking this.

This file contains various examples of expected output of sample
programs. These are run as part of the testsuite, as are the other
programs in the [test directory](../test).

## Basic syntax

Comments begin with `;` and continue to the end of the line.

A Malfunction input file consists of a single
s-expression. S-expressions (or "sexps") consist of `(`, a sequence of
whitespace-separated elements, and `)`, where elements are:
  - *Atoms*: sequences of ASCII letters, digits, or symbols (the exact set of allowed symbols isn't quite nailed down yet)
  - *Variables*: `\$` followed by an atom
  - *Strings*: double-quoted, with embedded `\` or `"` backslash-escaped
  - *s-expressions*: nested arbitrarily

The top-level sexp must begin with the atom `module`, followed
by a list of bindings (described under `let`, below), followed by an
sexp beginning with the atom `export`.

For inputs compiled with `malfunction compile` (that is, whole
programs), the `export` sexp must be empty. For instance, a program
which evaluates the single sexp `E` ignoring its result has this form:

    (module
      (_ E)
      (export))

Inputs compiled with `malfunction cmx` (that is, modules that are
later linked with other modules) may specify any number of values in
the `export` sexp, which must be in the same order as they are listed
in the corresponding `.mli` file.


## Numbers and arithmetic

There are several numeric types, and associated constant syntax:
  - int, e.g. `42`
  - int32, e.g. `42.i32`
  - int64, e.g. `42.i64`
  - bigint, e.g. `42.ibig`
  - float, e.g. `42.0`

`int32` and `int64` use 32-bit and 64-bit two's complement arithmetic,
with wrap on overflow. `int` uses either 31- or 63- bit two's
complement arithmetic (depending on system word size, and also
wrapping on overflow), and is generally fastest. `bigint` has
arbitrary precision. `float` uses IEEE754 double-precision (64-bit)
arithmetic.

Various numeric operations are defined:

  - *Arithmetic operations*: `+`, `-`, `*`, `/`, `%` (modulo), `neg` (unary negation)
  - *Bitwise operations*: `&`, `|`, `^`, `<<`, `>>` (zero-shifting), `a>>` (sign extending)
  - *Numeric comparisons*: `<`, `>`, `<=`, `>=`, `==`

All of these operations take one or two `int`s and return an `int`:

```test
(+ 10 (* 20 3))
=> 70
```

```test
(<< 1 5)
=> 32
```

These operations come in `int32`, `int64`, `bigint` and `float`
varieties, which may be used by suffixing `.i32`, `.i64`, `.big` or `.f64`
to the operation name. The bitwise operations are not available for
`float`s. The suffixed operations all take and return values of the
specified numeric type, except:

  - the shift operators (`<<`, `>>`, `a>>`) whose second argument (shift count) is always `int`
  - the comparison operators, whose result is always `int` (in fact, always `0` or `1`)

For example,

```test
(*.ibig 948324329804.ibig 8493208402394.ibig)
=> 8054316166085991599150776.ibig
```

```test
(>>.i32 32.i32 5)
=> 1.i32
```

```test
(+.f64 0.1 0.2)
=> 0.30000000000000004
```

As well as ordinary finite values, floats support infinite and NaN
values, available as the literals `infinity`, `neg_infinity` and
`nan`. Note that `nan` is unordered with respect to other floats, so
comparisons with it always return false.

Integer types are not automatically coerced, and behaviour is
undefined if the wrong types are passed to an operation. Explicit
conversions are done with `convert.FROM.TO`. When converting between
integer types, conversions from smaller to larger types sign-extend
and conversions from larger to smaller truncate. Conversions from an
integer type to float round to the nearest float, which may not be
exactly equal to the specified integer.

Conversions from float to integer type truncate the fractional
part. Currently, their behaviour is undefined if the input is outside
the representable range of the target type, although this might change
in the future.

```test
(convert.i32.i64 42.i32)
=> 42.i64
```

```test
(convert.f64.int 3.9)
=> 3
```

## Functions

Functions are defined using the following syntax, and close over all
bindings in scope:

    (lambda ($arg1 $arg2 $arg3) BODY)

Functions are applied using the following syntax:

    (apply FUNC ARG ARG ARG)

Multiple-argument functions are implicitly curried, and may be
partially applied (resulting in a closure) or applied to too many
arguments (resulting in an application of the returned value). For
instance,

```test
(apply (apply (lambda ($a $b) (+ $a $b)) 20) 22)
=> 42
```

```test
(apply (lambda ($a) (lambda ($b) (+ $a $b))) 20 22)
=> 42
```

However, performance will be higher if functions are applied to
exactly the right number of arguments.

Evaluation is eager: functions and arguments are evaluated before
their bodies. The function is evaluated before the arguments, and
arguments are evaluated left to right.

## Bindings

The atom `let` introduces a sequence of bindings:

    (let BINDING BINDING BINDING ... BODY)

Each binding is of one of the forms:

  - `($var EXP)`: binds `$var` to the result of evaluating `EXP`. `$var` scopes over subsequent bindings and the body.
  - `(_ EXP)`: evaluates `EXP` and ignores the result
  - `(rec ($VAR1 EXP1) ($VAR2 EXP2) ...)`: binds each `$VAR` mutually
    recursively. Each `EXP` must be of the form `(lambda
    ...)` or `(lazy ...)`. Bindings scope over themselves,
    each other, subsequent bindings, and the body.

For example, here is a definition of the "even" and "odd" predicates
on `int`s, and an application of them to check whether 42 is even (see
below for `if`):

```test
(let
  (rec
    ($even (lambda ($n) (if (<= $n 1) (== $n 0) (apply $odd (- $n 1)))))
    ($odd (lambda ($n) (if (<= $n 1) (== $n 1) (apply $even (- $n 1))))))
  ($res (apply $even 42))
  $res)
=> 1
```

The syntax `(seq EXP EXP...)` is equivalent to `(let (_ EXP) (_
EXP)... EXP)`, and can be used to write sequences of imperative
actions whose results are ignored.

## Blocks and fields

Blocks (tuples) are constructed using `(block (tag N) EXP EXP EXP
...)`, where `N` is a constant integer called the "tag" (an integer in
the range 0-199 which may be used with `switch` below) and each `EXP`
is a field of the resulting block.

Fields are projected from a block using `(field N EXP)`, where `N` is
an integer between 0 and one less than the length of the block.

```test
(let
  ($a (block (tag 0) 1 2 (block (tag 1) 0) 3))
  ($b (block (tag 0) (field 2 $a) (field 0 $a)))
  $b)
=> (block (tag 0) (block (tag 1) 0) 1)
```

Fields of blocks can only be accessed at constant, compile-time-known
offsets. For random access into a structure, see "Vectors" below.

## Conditionals

The general conditional expression is `switch`, of the form:

    (switch EXP
      (SEL SEL... EXP)
      (SEL SEL... EXP)
      ...)

The first `EXP` is evaluated, and matched against each case in the
order they appear. A case (of the form `(SEL SEL... EXP)`) matches if
any of its selectors (`SEL`) match. The result of the switch is the
result of evaluating the `EXP` of the first matching case. Selectors may be:

  - `42`: integers, matching themselves. Only `int`, not `int32`,
    `int64` or `bigint` may be matched. Use comparison operators,
    which always return ints, to switch on other integer types.
  - `(10 20)`: integer ranges, matching (in this example) any `n` where `10 <= n <= 20`
  - `_`: default case, matching any *integer*
  - `(tag 10)`: matches blocks with tag 10
  - `(tag _)`: matches any block.

Note that `_` matches only integers. To have a case handle all
integers and all blocks, write `(_ (tag _) EXP)`.

Selectors must be literal constants. To compare against runtime
values, use comparison operators.

For instance,

```test
(let
  ($sw (lambda ($n)
    (switch $n
      (5 (10 20) 100)
      ((15 50) 200)
      (_ 300)
      ((tag 10) 400))))
  ($a (apply $sw 5))
  ($b (apply $sw 10))
  ($c (apply $sw 50))
  ($d (apply $sw 60))
  ($e (apply $sw (block (tag 10))))
  (block (tag 0) $a $b $c $d $e))
=> (block (tag 0) 100 100 200 300 400)
```

Behaviour is undefined if no cases match. If you are compiling a
conditional statement to Malfunction and cannot prove that all cases
are handled, you must add an explicit default case.

The expression `(if A B C)` is equivalent to:

    (switch A
      (0 C)
      (_ (tag _) B))

That is, `C` is executed if `A` evaluates to zero, and `C` otherwise.

Complex mixtures of conditions in `switch` expressions perform well -
the OCaml compiler generates good code for pattern-matching.

## Vectors

Vectors are mutable, fixed-length sequences of slots. The slots are
numbered from 0 to one less than the length of the vector, and support
random access.

  - `(makevec LEN VAL)`: creates a vector of length `LEN` (must evaluate to a
    nonnegative integer) initially containing the result of evaluating `VAL` in all slots.
  - `(load VEC IDX)`: evaluates `VEC` (which must evaluate to a
    vector) and `IDX` (which must evaluate to an integer), and returns
    the value of the `IDX`'th slot (which must be in bounds).
  - `(store VEC IDX VAL)`: evaluates `VEC` (a vector), `IDX` (an
    in-bounds index) and `VAL`, and stores `VAL` in the `IDX`'th slot.
  - `(length VEC)`: evaluates `VEC` (a vector) and returns its length.

As well as standard vectors, byte vectors are also available. They
have the same semantics as vectors, except that the operations are
suffixed `.byte` (`makevec.byte`, etc.) and they may only be used to
store integers in the range 0-255.

Behaviour is undefined if byte vector operations are used on standard
vectors, or vice versa.

String literals (`"hello"`) return byte vectors.

## Lazy evaluation

A *lazily-evaluated* expression is one that's not computed until it's
needed. The expression `(lazy E)` constructs a lazy value that wraps
the expression `E` but does not evaluate it immediately. When the lazy
value is examined using `(force $lazyval)`, `E` will be computed.

`E` is evaluated at most once for a given `(lazy E)`. If the resulting
value is `force`d twice, then the value computed by `E` is cached.

If evaluating `E` produces side effects, these occur at the time that
`E` is first forced. For instance:

```test
(let
  ($box (makevec 1 42))
  ($thunk
    (lazy (let
      ($val (load $box 0))
      (_ (store $box 0 (+ $val 1)))
      $val)))
  (block (tag 0)
    (load $box 0)
    (force $thunk)
    (load $box 0)
    (force $thunk)))
=> (block (tag 0) 42 42 43 42)
```

## Accessing OCaml values

OCaml values can be accessed from Malfunction programs by specifying a
module path using `global`. For instance, the OCaml function
`Stdlib.print_string` is referred to as `(global $Stdlib $print_string)`.

As well as calling OCaml functions, certain OCaml values can be
directly manipulated. The integer types `int`, `int32` and `int64`
correspond to the OCaml types `int`, `Int32.t` and `Int64.t`, OCaml
tuples are blocks with tag 0, and OCaml algebraic data types are
represented as a combination of ints and blocks as described in
section
[19.3.4 of the OCaml manual, "Concrete data types"](https://v2.ocaml.org/manual/intfc.html#ss:c-concrete-datatypes).
