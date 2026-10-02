object Main {

sealed trait Bool
final case class True() extends Bool
final case class False() extends Bool


sealed trait Nat
final case class O() extends Nat
final case class S(_1: Nat) extends Nat


sealed trait MyList[a]
final case class MyNil[a]() extends MyList[a]
final case class MyCons[a](_1: a, _2: MyList[a]) extends MyList[a]


def myLength[t1]: MyList[t1] => Nat =
    (l: MyList[t1]) => 
    l match {
    case MyNil() => O()
    case MyCons(_, t) => S(myLength[t1](t))
    }

def myMap[t1, t2]: (t1 => t2) => MyList[t1] => MyList[t2] =
    (f: t1 => t2) => (l: MyList[t1]) => 
    l match {
    case MyNil() => MyNil()
    case MyCons(a, t) => MyCons(f(a), myMap[t1, t2](f)(t))
    }

def myAppend[t1]: MyList[t1] => MyList[t1] => MyList[t1] =
    (l1: MyList[t1]) => (l2: MyList[t1]) => 
    (l1 match {
     case MyNil() => l2
     case MyCons(a, t) => MyCons(a, myAppend[t1](t)(l2))
     }).asInstanceOf[MyList[t1]]

def myFold[t1, t2]: (t2 => t1 => t2) => t2 => MyList[t1] => t2 =
    (f: t2 => t1 => t2) => (acc: t2) => (l: MyList[t1]) => 
    l match {
    case MyNil() => acc
    case MyCons(a, t) => myFold[t1, t2](f)((f(acc)(a)))(t)
    }

def myAll[t1]: (t1 => Bool) => MyList[t1] => Bool =
    (f: t1 => Bool) => (l: MyList[t1]) => 
    l match {
    case MyNil() => True()
    case MyCons(a, t) =>
      (f(a)) match {
      case True() => myAll[t1](f)(t)
      case False() => False()
      }
    }

def compose[t1, t2, t3]: (t2 => t3) => (t1 => t2) => t1 => t3 =
  (f: t2 => t3) => (g: t1 => t2) => (x: t1) => 
    f((g(x)))

def emptyList[t1]: MyList[t1] = MyNil()

}

