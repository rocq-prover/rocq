Inductive T := C (c := I) (n : nat).
Arguments C {_}.
Check fun x => match x return True with C i => i end.
