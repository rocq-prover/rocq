object Main {

sealed trait Nat
final case class O() extends Nat
final case class S(_1: Nat) extends Nat


def isEven: Nat => Boolean =
    (n: Nat) => 
    (n match {
     case O() => true
     case S(p) => isOdd(p)
     }).asInstanceOf[Boolean]

def isOdd: Nat => Boolean =
    (n: Nat) => 
    (n match {
     case O() => false
     case S(p) => isEven(p)
     }).asInstanceOf[Boolean]

val myNot: Boolean => Boolean =
  (b: Boolean) => 
    (b match {
     case true => false
     case false => true
     }).asInstanceOf[Boolean]

}

