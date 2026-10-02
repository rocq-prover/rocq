object Main {

sealed trait Nat
final case class O() extends Nat
final case class S(_1: Nat) extends Nat


final case class MkPoint(px: Nat, py: Nat)
type Point = MkPoint

val swap: Point => Point = (p: Point) => 
    MkPoint(p.py, p.px)

type Box[a] = a
// singleton inductive, whose constructor was MkBox

def mapBox[t1, t2]: (t1 => t2) => Box[t1] => Box[t2] = (f: t1 => t2) => 
    f

}

