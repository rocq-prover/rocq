Record lattice' T (carrier := T) := { top' : T ; bottom' : T }.
Scheme Equality for lattice'.

Scheme Equality for list.
Record r2 A (B := list A) C := { f1 : B ; f2 : C ; f3 : A }.
Scheme Equality for r2.
