object Main {

sealed trait Nat
final case class O() extends Nat
final case class S(_1: Nat) extends Nat


def addNat: Nat => Nat => Nat =
    (n: Nat) => (m: Nat) => 
    n match {
    case O() => m
    case S(p) => S(addNat(p)(m))
    }

def mulNat: Nat => Nat => Nat =
    (n: Nat) => (m: Nat) => 
    n match {
    case O() => O()
    case S(p) => addNat(m)((mulNat(p)(m)))
    }

}

