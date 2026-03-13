
Module Type CmpType.
  Parameter t : Type.
End CmpType.

Module Type MAP.
  Declare Module K: CmpType.
End MAP.

Module Mmake (K':CmpType).
  Module K := K'.
End Mmake.

Module Tagged(C:CmpType).
  Module Mt : MAP with Definition K.t := C.t := Mmake C.
End Tagged.

Require Extraction.
Extraction Tagged.
