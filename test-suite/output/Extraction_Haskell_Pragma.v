Require Import Stdlib.extraction.Extraction.
Extraction Language Haskell.
Set Extraction File Pragma "OPTIONS_GHC -cpp -XMagicHash".

Recursive Extraction nat.
