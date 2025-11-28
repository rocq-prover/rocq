Goal True.
Proof.
try (assert (H : True) by abstract constructor using foo; fail).
Fail exact foo.
Abort.
