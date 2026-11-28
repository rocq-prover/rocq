Require Import ForgedAliases.Lib.

Module Type T.
  Parameter lemma : eq bool A.X.d false.
End T.

Module G : T := F A.
