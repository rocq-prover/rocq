From Corelib Require Extraction.

Extraction Language OCaml.

Fixpoint recursive_callback (n : nat) : nat :=
  match n with
  | O => O
  | S k => recursive_callback k
  end.

Extract Callback "recursive_alias" recursive_callback.
Extraction recursive_callback.

Fixpoint even (n : nat) : bool :=
  match n with
  | O => true
  | S k => odd k
  end
with odd (n : nat) : bool :=
  match n with
  | O => false
  | S k => even k
  end.

Extract Callback "even_alias" even.
Extract Callback "odd_alias" odd.
Extraction even.
Extraction TestCompile recursive_callback even.
