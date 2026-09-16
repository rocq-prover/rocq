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

sealed trait Tree[a]
final case class Leaf[a]() extends Tree[a]
final case class Node[a](_1: Tree[a], _2: a, _3: Tree[a]) extends Tree[a]


def treeSum: Tree[Nat] => Nat =
    (t: Tree[Nat]) => 
    t match {
    case Leaf() => O()
    case Node(l, x, r) => addNat((treeSum(l)))((addNat(x)((treeSum(r)))))
    }

def treeMap[t1, t2]: (t1 => t2) => Tree[t1] => Tree[t2] =
    (f: t1 => t2) => (t: Tree[t1]) => 
    t match {
    case Leaf() => Leaf()
    case Node(l, x, r) =>
      Node(treeMap[t1, t2](f)(l), f(x), treeMap[t1, t2](f)(r))
    }

sealed trait MyOption[a]
final case class MyNone[a]() extends MyOption[a]
final case class MySome[a](_1: a) extends MyOption[a]


def optionMap[t1, t2]: (t1 => t2) => MyOption[t1] => MyOption[t2] =
  (f: t1 => t2) => (o: MyOption[t1]) => 
    o match {
    case MyNone() => MyNone()
    case MySome(a) => MySome(f(a))
    }

}

