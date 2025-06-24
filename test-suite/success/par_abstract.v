Axiom T : Type.
Set Debug "ustate".
Lemma foo : True * Type.
Proof.
  Show Universes.
  split.
  Show Universes.
  Show Proof.
Show Existentials.
Set Debug "univMinim".
par: abstract (exact I || exact T).
Defined.

(*
Debug:
88630:tactic:1:1:0 [ustate]
                     Calling process_universe_constraints with: Type(par_abstract.21) <= Type(par_abstract.24)
                     Context: {par_abstract.26 par_abstract.25 par_abstract.24}
Debug:
88630:tactic:1:1:0 [ustate]
                     process_constraints terminated with: UNIVERSE VARIABLES:
                                                           {par_abstract.26 par_abstract.25
                                                            par_abstract.24}
                                                          DEMOTED (GLOBAL) UNIVERSE VARIABLES:
                                                          FLEXIBLE UNIVERSE VARIABLES:
                                                           {par_abstract.26 par_abstract.25}
                                                          UNIVERSES:
                                                           0 <= par_abstract.24
                                                             <= par_abstract.25
                                                             <= par_abstract.26
                                                           T.u0 <= par_abstract.24
                                                           par_abstract.22 = 0
                                                           par_abstract.23 = par_abstract.24+1
                                                           par_abstract.24 < par_abstract.26
                                                          SORTS:
                                                           α1 := Type
                                                           α2 := Type |=
                                                             α1 <-> Type
                                                             α2 <-> Type
                                                             Prop -> SProp
                                                             Type -> Prop
                                                                  -> SProp
                                                          VARIANCES:
                                                           par_abstract.26
                                                           par_abstract.25
                                                           par_abstract.24: infer: = in type,
                                                                    predicative
                                                          WEAK CONSTRAINTS:
Debug:
[ustate]
  Union of UNIVERSE VARIABLES:
            {par_abstract.26 par_abstract.25 par_abstract.24}
           DEMOTED (GLOBAL) UNIVERSE VARIABLES:
           FLEXIBLE UNIVERSE VARIABLES:
            {par_abstract.26 par_abstract.25}
           UNIVERSES:
            0 <= par_abstract.24
              <= par_abstract.25
              <= par_abstract.26
            par_abstract.22 = 0
            par_abstract.23 = par_abstract.24+1
            par_abstract.24 < par_abstract.26
           SORTS:
            α1 := Type
            α2 := Type |= α1 <-> Type
                          α2 <-> Type
                          Prop -> SProp
                          Type -> Prop
                               -> SProp
           VARIANCES:
            par_abstract.26
            par_abstract.25
            par_abstract.24: infer: = in type,  predicative
           WEAK CONSTRAINTS:
            and
  UNIVERSE VARIABLES:
   {par_abstract.26 par_abstract.25 par_abstract.24}
  DEMOTED (GLOBAL) UNIVERSE VARIABLES:
  FLEXIBLE UNIVERSE VARIABLES:
   {par_abstract.26 par_abstract.25}
  UNIVERSES:
   0 <= par_abstract.24
     <= par_abstract.25
     <= par_abstract.26
   par_abstract.22 = 0
   par_abstract.23 = par_abstract.24+1
   par_abstract.24 < par_abstract.26
  SORTS:
   α1 := Type
   α2 := Type |= α1 <-> Type
                 α2 <-> Type
                 Prop -> SProp
                 Type -> Prop
                      -> SProp
  VARIANCES:
   par_abstract.26
   par_abstract.25
   par_abstract.24: infer: = in type,  predicative
  WEAK CONSTRAINTS:
Debug:
[ustate]
  Levelsr = {par_abstract.26 par_abstract.25 par_abstract.24 par_abstract.23 par_abstract.22}
Debug: [ustate] Levelsr = {}
Debug:
[ustate]
  Union of substitutions = 0 <= par_abstract.24
                             <= par_abstract.25
                             <= par_abstract.26
  par_abstract.22 = 0
  par_abstract.23 = par_abstract.24+1
  par_abstract.24 < par_abstract.26
Debug:
[ustate]
  Union = UNIVERSE VARIABLES:
           {par_abstract.26 par_abstract.25 par_abstract.24}
          DEMOTED (GLOBAL) UNIVERSE VARIABLES:
          FLEXIBLE UNIVERSE VARIABLES:
           {par_abstract.26 par_abstract.25}
          UNIVERSES:
           0 <= par_abstract.24
             <= par_abstract.25
             <= par_abstract.26
           par_abstract.22 = 0
           par_abstract.23 = par_abstract.24+1
           par_abstract.24 < par_abstract.26
          SORTS:
           α1 := Type
           α2 := Type |= Prop -> SProp
                         Type -> α1
                              -> α2
                              -> Prop
                              -> SProp
          VARIANCES:
           par_abstract.26
           par_abstract.25
           par_abstract.24: infer: = in type,  predicative
          WEAK CONSTRAINTS:
Debug:
[univMinim]
  Minimizing context: 0 <= par_abstract.24
                        <= par_abstract.25
                        <= par_abstract.26
  par_abstract.22 = 0
  par_abstract.23 = par_abstract.24+1
  par_abstract.24 < par_abstract.26
  Local variables: {par_abstract.26 par_abstract.25 par_abstract.24}
  Flexible variables: {par_abstract.26 par_abstract.25}
  Variances: par_abstract.26
             par_abstract.25
             par_abstract.24: infer: = in type,  predicative
  Above prop: {par_abstract.25}
  Above zero: {}
  Weak constraints
  In non-partial mode
   solving flexibles respecting variances information
Debug:
[univMinim]
  After minimization:
  Local variables: {par_abstract.24}
  Flexible variables: {}
  Variances: par_abstract.24: infer: = in type,  predicative
  0 <= par_abstract.24
  par_abstract.22 = 0
  par_abstract.23 = par_abstract.24+1
  par_abstract.25 = 0
  par_abstract.26 = par_abstract.24+1
Debug:
[ustate]
  Restricting universe context: UNIVERSE VARIABLES:
                                 {par_abstract.24}
                                DEMOTED (GLOBAL) UNIVERSE VARIABLES:
                                FLEXIBLE UNIVERSE VARIABLES:
                                 {}
                                UNIVERSES:
                                 0 <= par_abstract.24
                                 par_abstract.22 = 0
                                 par_abstract.23 = par_abstract.24+1
                                 par_abstract.25 = 0
                                 par_abstract.26 = par_abstract.24+1
                                SORTS:
                                 α1 := Type
                                 α2 := Type |= Prop -> SProp
                                               Type -> α1
                                                    -> α2
                                                    -> Prop
                                                    -> SProp
                                VARIANCES:
                                 par_abstract.24: infer: = in type,  predicative
                                WEAK CONSTRAINTS:
                                 to {par_abstract.24}
Debug:
[ustate]
  Rigid context set of UNIVERSE VARIABLES:
                        {par_abstract.24}
                       DEMOTED (GLOBAL) UNIVERSE VARIABLES:
                       FLEXIBLE UNIVERSE VARIABLES:
                        {}
                       UNIVERSES:
                        0 <= par_abstract.24
                        par_abstract.22 = 0
                        par_abstract.23 = par_abstract.24+1
                        par_abstract.25 = 0
                        par_abstract.26 = par_abstract.24+1
                       SORTS:
                        α1 := Type
                        α2 := Type |= Prop -> SProp
                                      Type -> α1
                                           -> α2
                                           -> Prop
                                           -> SProp
                       VARIANCES:
                        par_abstract.24: infer: = in type,  predicative
                       WEAK CONSTRAINTS:
   = {par_abstract.24} |=
Debug:
[ustate]
  Rigid context set of UNIVERSE VARIABLES:
                        {par_abstract.24}
                       DEMOTED (GLOBAL) UNIVERSE VARIABLES:
                       FLEXIBLE UNIVERSE VARIABLES:
                        {}
                       UNIVERSES:
                        0 <= par_abstract.24
                        par_abstract.22 = 0
                        par_abstract.23 = par_abstract.24+1
                        par_abstract.25 = 0
                        par_abstract.26 = par_abstract.24+1
                       SORTS:
                        α1 := Type
                        α2 := Type |= Prop -> SProp
                                      Type -> α1
                                           -> α2
                                           -> Prop
                                           -> SProp
                       VARIANCES:
                        par_abstract.24: infer: = in type,  predicative
                       WEAK CONSTRAINTS:
   = {par_abstract.24} |=
Debug:
[ustate]
  demote_global_univs:{par_abstract.24} |=
  From: UNIVERSE VARIABLES:
         {par_abstract.24}
        DEMOTED (GLOBAL) UNIVERSE VARIABLES:
        FLEXIBLE UNIVERSE VARIABLES:
         {}
        UNIVERSES:
         0 <= par_abstract.24
         par_abstract.22 = 0
         par_abstract.23 = par_abstract.24+1
         par_abstract.25 = 0
         par_abstract.26 = par_abstract.24+1
        SORTS:
         α1 := Type
         α2 := Type |= Prop -> SProp
                       Type -> α1
                            -> α2
                            -> Prop
                            -> SProp
        VARIANCES:
         par_abstract.24: infer: = in type,  predicative
        WEAK CONSTRAINTS:
Debug:
[ustate]
  Union of UNIVERSE VARIABLES:
            {}
           DEMOTED (GLOBAL) UNIVERSE VARIABLES:
            {par_abstract.24} |=
           FLEXIBLE UNIVERSE VARIABLES:
            {}
           UNIVERSES:
            0 <= par_abstract.24
            par_abstract.22 = 0
            par_abstract.23 = par_abstract.24+1
            par_abstract.25 = 0
            par_abstract.26 = par_abstract.24+1
           SORTS:
            α1 := Type
            α2 := Type |= Prop -> SProp
                          Type -> α1
                               -> α2
                               -> Prop
                               -> SProp
           VARIANCES:
            par_abstract.24: infer: = in type,  predicative
           WEAK CONSTRAINTS:
            and
  UNIVERSE VARIABLES:
   {par_abstract.26 par_abstract.25 par_abstract.24}
  DEMOTED (GLOBAL) UNIVERSE VARIABLES:
  FLEXIBLE UNIVERSE VARIABLES:
   {par_abstract.26 par_abstract.25}
  UNIVERSES:
   0 <= par_abstract.24
     <= par_abstract.25
     <= par_abstract.26
   T.u0 <= par_abstract.24
   par_abstract.22 = 0
   par_abstract.23 = par_abstract.24+1
   par_abstract.24 < par_abstract.26
  SORTS:
   α1 := Type
   α2 := Type |= α1 <-> Type
                 α2 <-> Type
                 Prop -> SProp
                 Type -> Prop
                      -> SProp
  VARIANCES:
   par_abstract.26
   par_abstract.25
   par_abstract.24: infer: = in type,  predicative
  WEAK CONSTRAINTS:
Debug:
[ustate]
  Levelsr = {par_abstract.26 par_abstract.25 par_abstract.24 par_abstract.23 par_abstract.22}
Debug: [ustate] Levelsr = {par_abstract.24}
Debug:
[ustate]
  Union of substitutions = 0 <= par_abstract.24
  par_abstract.22 = 0
  par_abstract.23 = par_abstract.24+1
  par_abstract.25 = 0
  par_abstract.26 = par_abstract.24+1
Debug:
[ustate]
  Union = UNIVERSE VARIABLES:
           {par_abstract.26 par_abstract.25 par_abstract.24}
          DEMOTED (GLOBAL) UNIVERSE VARIABLES:
           {par_abstract.24} |=
          FLEXIBLE UNIVERSE VARIABLES:
           {par_abstract.26 par_abstract.25}
          UNIVERSES:
           0 <= par_abstract.24
           T.u0 <= par_abstract.24
           par_abstract.22 = 0
           par_abstract.23 = par_abstract.24+1
           par_abstract.25 = 0
           par_abstract.26 = par_abstract.24+1
          SORTS:
           α1 := Type
           α2 := Type |= Prop -> SProp
                         Type -> α1
                              -> α2
                              -> Prop
                              -> SProp
          VARIANCES:
           par_abstract.26
           par_abstract.25
           par_abstract.24: infer: = in type,  predicative
          WEAK CONSTRAINTS:
Debug:
[univMinim]
  Minimizing context: 0 <= par_abstract.24
  T.u0 <= par_abstract.24
  par_abstract.22 = 0
  par_abstract.23 = par_abstract.24+1
  par_abstract.25 = 0
  par_abstract.26 = par_abstract.24+1
  Local variables: {par_abstract.26 par_abstract.25 par_abstract.24}
  Flexible variables: {par_abstract.26 par_abstract.25}
  Variances: par_abstract.26
             par_abstract.25
             par_abstract.24: infer: = in type,  predicative
  Above prop: {par_abstract.25}
  Above zero: {}
  Weak constraints
  In non-partial mode
   solving flexibles respecting variances information
Debug:
[univMinim]
  After minimization:
  Local variables: {par_abstract.26 par_abstract.25 par_abstract.24}
  Flexible variables: {par_abstract.26 par_abstract.25}
  Variances: par_abstract.26
             par_abstract.25
             par_abstract.24: infer: = in type,  predicative
  0 <= par_abstract.24
  T.u0 <= par_abstract.24
  par_abstract.22 = 0
  par_abstract.23 = par_abstract.24+1
  par_abstract.25 = 0
  par_abstract.26 = par_abstract.24+1
Debug:
[ustate]
  Restricting universe context: UNIVERSE VARIABLES:
                                 {par_abstract.26 par_abstract.25 par_abstract.24}
                                DEMOTED (GLOBAL) UNIVERSE VARIABLES:
                                 {par_abstract.24} |=
                                FLEXIBLE UNIVERSE VARIABLES:
                                 {par_abstract.26 par_abstract.25}
                                UNIVERSES:
                                 0 <= par_abstract.24
                                 T.u0 <= par_abstract.24
                                 par_abstract.22 = 0
                                 par_abstract.23 = par_abstract.24+1
                                 par_abstract.25 = 0
                                 par_abstract.26 = par_abstract.24+1
                                SORTS:
                                 α1 := Type
                                 α2 := Type |= Prop -> SProp
                                               Type -> α1
                                                    -> α2
                                                    -> Prop
                                                    -> SProp
                                VARIANCES:
                                 par_abstract.26
                                 par_abstract.25
                                 par_abstract.24: infer: = in type,  predicative
                                WEAK CONSTRAINTS:
                                 to {par_abstract.26 par_abstract.25 par_abstract.24}
Debug:
[ustate]
  Rigid context set of UNIVERSE VARIABLES:
                        {par_abstract.26 par_abstract.25 par_abstract.24}
                       DEMOTED (GLOBAL) UNIVERSE VARIABLES:
                        {par_abstract.24} |=
                       FLEXIBLE UNIVERSE VARIABLES:
                        {par_abstract.26 par_abstract.25}
                       UNIVERSES:
                        0 <= par_abstract.24
                        T.u0 <= par_abstract.24
                        par_abstract.22 = 0
                        par_abstract.23 = par_abstract.24+1
                        par_abstract.25 = 0
                        par_abstract.26 = par_abstract.24+1
                       SORTS:
                        α1 := Type
                        α2 := Type |= Prop -> SProp
                                      Type -> α1
                                           -> α2
                                           -> Prop
                                           -> SProp
                       VARIANCES:
                        par_abstract.26
                        par_abstract.25
                        par_abstract.24: infer: = in type,  predicative
                       WEAK CONSTRAINTS:
   = {par_abstract.26 par_abstract.25} |=
       par_abstract.21 <= par_abstract.24
       par_abstract.25 = 0
       par_abstract.26 = par_abstract.24+1
Debug:
[ustate]
  Rigid context set of UNIVERSE VARIABLES:
                        {par_abstract.26 par_abstract.25 par_abstract.24}
                       DEMOTED (GLOBAL) UNIVERSE VARIABLES:
                        {par_abstract.24} |=
                       FLEXIBLE UNIVERSE VARIABLES:
                        {par_abstract.26 par_abstract.25}
                       UNIVERSES:
                        0 <= par_abstract.24
                        T.u0 <= par_abstract.24
                        par_abstract.22 = 0
                        par_abstract.23 = par_abstract.24+1
                        par_abstract.25 = 0
                        par_abstract.26 = par_abstract.24+1
                       SORTS:
                        α1 := Type
                        α2 := Type |= Prop -> SProp
                                      Type -> α1
                                           -> α2
                                           -> Prop
                                           -> SProp
                       VARIANCES:
                        par_abstract.26
                        par_abstract.25
                        par_abstract.24: infer: = in type,  predicative
                       WEAK CONSTRAINTS:
   = {par_abstract.26 par_abstract.25} |=
       par_abstract.21 <= par_abstract.24
       par_abstract.25 = 0
       par_abstract.26 = par_abstract.24+1
Error: Universe inconsistency. Cannot enforce par_abstract.25 = Set because 0 < 1
≤ par_abstract.25.
*)
(*

Debug: [ustate] Calling process_universe_constraints with: Prop <= α9
                   Context: {}
Debug:
[ustate]
  process_constraints terminated with: UNIVERSE VARIABLES:
                                        {}
                                       DEMOTED (GLOBAL) UNIVERSE VARIABLES:
                                       FLEXIBLE UNIVERSE VARIABLES:
                                        {}
                                       UNIVERSES:
                                       SORTS:
                                        α9 >= Prop |= Prop -> SProp
                                                      Type -> α9
                                                           -> Prop
                                                           -> SProp
                                       WEAK CONSTRAINTS:
Debug:
[ustate]
  Calling process_universe_constraints with: Prop <= QSort(α9,
  par_abstract.42)
  Context: {par_abstract.42}
Debug:
[ustate]
  process_constraints terminated with: UNIVERSE VARIABLES:
                                        {par_abstract.42}
                                       DEMOTED (GLOBAL) UNIVERSE VARIABLES:
                                       FLEXIBLE UNIVERSE VARIABLES:
                                        {par_abstract.42}
                                       UNIVERSES:
                                        0 <= par_abstract.42
                                       SORTS:
                                        α9 >= Prop |= Prop -> SProp
                                                      Type -> α9
                                                           -> Prop
                                                           -> SProp
                                       WEAK CONSTRAINTS:
Debug: [ustate] Calling process_universe_constraints with: Prop <= α10
          Context: {par_abstract.42}
Debug:
[ustate]
  process_constraints terminated with: UNIVERSE VARIABLES:
                                        {par_abstract.42}
                                       DEMOTED (GLOBAL) UNIVERSE VARIABLES:
                                       FLEXIBLE UNIVERSE VARIABLES:
                                        {par_abstract.42}
                                       UNIVERSES:
                                        0 <= par_abstract.42
                                       SORTS:
                                        α9 >= Prop
                                        α10 >= Prop |=
                                          Prop -> SProp
                                          Type -> α9
                                               -> α10
                                               -> Prop
                                               -> SProp
                                       WEAK CONSTRAINTS:
Debug:
[ustate]
  Calling process_universe_constraints with: Type(par_abstract.44+1) <= QSort(α10,
  par_abstract.43)
  Context: {par_abstract.44 par_abstract.43 par_abstract.42}
Debug:
[ustate]
  process_constraints terminated with: UNIVERSE VARIABLES:
                                        {par_abstract.44 par_abstract.43 par_abstract.42}
                                       DEMOTED (GLOBAL) UNIVERSE VARIABLES:
                                       FLEXIBLE UNIVERSE VARIABLES:
                                        {par_abstract.43 par_abstract.42}
                                       UNIVERSES:
                                        0 <= par_abstract.42
                                          <= par_abstract.43
                                          <= par_abstract.44
                                        par_abstract.44 < par_abstract.43
                                       SORTS:
                                        α9 >= Prop
                                        α10 := Type |=
                                          α10 <-> Type
                                          Prop -> SProp
                                          Type -> α9
                                               -> Prop
                                               -> SProp
                                       WEAK CONSTRAINTS:
Debug:
[ustate]
  Rigid context set of UNIVERSE VARIABLES:
                        {par_abstract.44 par_abstract.43 par_abstract.42}
                       DEMOTED (GLOBAL) UNIVERSE VARIABLES:
                       FLEXIBLE UNIVERSE VARIABLES:
                        {par_abstract.43 par_abstract.42}
                       UNIVERSES:
                        0 <= par_abstract.42
                          <= par_abstract.43
                          <= par_abstract.44
                        par_abstract.44 < par_abstract.43
                       SORTS:
                        α9 >= Prop
                        α10 := Type |= α10 <-> Type
                                       Prop -> SProp
                                       Type -> α9
                                            -> Prop
                                            -> SProp
                       WEAK CONSTRAINTS:
   = {par_abstract.44 par_abstract.43 par_abstract.42} |= par_abstract.44+1 <= par_abstract.43
Debug:
[ustate]
  Restricting universe context: UNIVERSE VARIABLES:
                                 {par_abstract.44}
                                DEMOTED (GLOBAL) UNIVERSE VARIABLES:
                                FLEXIBLE UNIVERSE VARIABLES:
                                 {}
                                UNIVERSES:
                                 0 <= par_abstract.44
                                 par_abstract.42 = 0
                                 par_abstract.43 = par_abstract.44+1
                                SORTS:
                                 α9 := Type
                                 α10 := Type |=
                                   α9 <-> Type
                                   α10 <-> Type
                                   Prop -> SProp
                                   Type -> Prop
                                        -> SProp
                                VARIANCES:
                                 par_abstract.44: infer: = in type,  predicative
                                WEAK CONSTRAINTS:
                                 to {par_abstract.44}
Debug:
[ustate]
  Rigid context set of UNIVERSE VARIABLES:
                        {par_abstract.44}
                       DEMOTED (GLOBAL) UNIVERSE VARIABLES:
                       FLEXIBLE UNIVERSE VARIABLES:
                        {}
                       UNIVERSES:
                        0 <= par_abstract.44
                        par_abstract.42 = 0
                        par_abstract.43 = par_abstract.44+1
                       SORTS:
                        α9 := Type
                        α10 := Type |= α9 <-> Type
                                       α10 <-> Type
                                       Prop -> SProp
                                       Type -> Prop
                                            -> SProp
                       VARIANCES:
                        par_abstract.44: infer: = in type,  predicative
                       WEAK CONSTRAINTS:
   = {par_abstract.44} |=
Debug:
[ustate]
  Rigid context set of UNIVERSE VARIABLES:
                        {par_abstract.44}
                       DEMOTED (GLOBAL) UNIVERSE VARIABLES:
                       FLEXIBLE UNIVERSE VARIABLES:
                        {}
                       UNIVERSES:
                        0 <= par_abstract.44
                        par_abstract.42 = 0
                        par_abstract.43 = par_abstract.44+1
                       SORTS:
                        α9 := Type
                        α10 := Type |= α9 <-> Type
                                       α10 <-> Type
                                       Prop -> SProp
                                       Type -> Prop
                                            -> SProp
                       VARIANCES:
                        par_abstract.44: infer: = in type,  predicative
                       WEAK CONSTRAINTS:
   = {par_abstract.44} |=



Debug:
[ustate]
  Calling process_universe_constraints with: Prop <= Type(par_abstract.45)
  Context: {par_abstract.46 par_abstract.45 par_abstract.44}
Debug:
[ustate]
  process_constraints terminated with: UNIVERSE VARIABLES:
                                        {par_abstract.46 par_abstract.45 par_abstract.44}
                                       DEMOTED (GLOBAL) UNIVERSE VARIABLES:
                                       FLEXIBLE UNIVERSE VARIABLES:
                                        {par_abstract.46 par_abstract.45}
                                       UNIVERSES:
                                        0 <= par_abstract.44
                                          <= par_abstract.45
                                          <= par_abstract.46
                                        par_abstract.42 = 0
                                        par_abstract.43 = par_abstract.44+1
                                       SORTS:
                                        α9 := Type
                                        α10 := Type |=
                                          α9 <-> Type
                                          α10 <-> Type
                                          Prop -> SProp
                                          Type -> Prop
                                               -> SProp
                                       VARIANCES:
                                        par_abstract.46
                                        par_abstract.45
                                        par_abstract.44: infer: = in type,  predicative
                                       WEAK CONSTRAINTS:
Debug:
[ustate]
  Calling process_universe_constraints with: Type(par_abstract.44+1) <= Type(par_abstract.46)
  Context: {par_abstract.46 par_abstract.45 par_abstract.44}
Debug:
[ustate]
  process_constraints terminated with: UNIVERSE VARIABLES:
                                        {par_abstract.46 par_abstract.45 par_abstract.44}
                                       DEMOTED (GLOBAL) UNIVERSE VARIABLES:
                                       FLEXIBLE UNIVERSE VARIABLES:
                                        {par_abstract.46 par_abstract.45}
                                       UNIVERSES:
                                        0 <= par_abstract.44
                                          <= par_abstract.45
                                          <= par_abstract.46
                                        par_abstract.42 = 0
                                        par_abstract.43 = par_abstract.44+1
                                        par_abstract.44 < par_abstract.46
                                       SORTS:
                                        α9 := Type
                                        α10 := Type |=
                                          α9 <-> Type
                                          α10 <-> Type
                                          Prop -> SProp
                                          Type -> Prop
                                               -> SProp
                                       VARIANCES:
                                        par_abstract.46
                                        par_abstract.45
                                        par_abstract.44: infer: = in type,  predicative
                                       WEAK CONSTRAINTS:

*)

(* Yes, these names are generated hence
   the test is fragile.  I want to assert
   that abstract was correctly handled
   by par: *)
Check foo_subproof.
Check foo_subproof0.
Check (refl_equal _ :
  foo =
  pair foo_subproof foo_subproof0).

Lemma bar : True * Type.
Proof.
  split.
  par: (exact I || exact T).
Defined.
Check (refl_equal _ :
  bar = pair I T).
