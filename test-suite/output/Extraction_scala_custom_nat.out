object Main {

val add: Int => Int => Int = ((n: Int) => (m: Int) => n + m)

val mul: Int => Int => Int = ((n: Int) => (m: Int) => n * m)

def fact: Int => Int =
    (n: Int) => 
    ((((fO: Any => Any) => (fS: Any => Any) => (n: Int) =>
      if (n == 0) fO(()) else fS(n - 1))
        (((_: Any) => ((n: Int) => n + 1)((0).asInstanceOf[Int])))
        (((p: Any) => mul(n)((fact((p).asInstanceOf[Int])))))
        (n))).asInstanceOf[Int]

}

