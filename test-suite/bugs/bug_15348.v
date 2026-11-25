Module Type E. End E.
Module Type T (X:E). End T.

Fail Module M : T.
Fail Module M <: T.
Fail Module M (X:E) : T.
Fail Module M (X:E) <: T.
Fail Module M <: E <: T.

Module M (X:E) <: E.
End M.

Module F (X:E). End F.
Module M1 : T := F.
Module M2 <: T := F.
Declare Module M3 : T.
