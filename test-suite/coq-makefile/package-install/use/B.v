From Foo Require A.
From Plug Require Loader.

Definition y := A.x.

Check eq_refl : S y = Loader.z.
