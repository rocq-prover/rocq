Declare ML Module "rocq-test-suite.attribute".

#[print]
Definition foo : True := I.

#[print]
Definition bar : False -> False := fun x => x.

Fail #[error]
Definition baz : False -> False := fun x => x.
