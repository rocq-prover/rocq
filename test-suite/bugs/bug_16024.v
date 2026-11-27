Module Type T. End T.

Module F (E : T) := E.

Module Type FT (X:T). End FT.

Module M := F <+ FT.
