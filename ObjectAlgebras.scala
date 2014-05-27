trait ObjectAlgebras {
  trait IntAlg[A] {
    def int(x: Int): A
    def add(e1: A, e2: A): A
  }

  def make3Plus5[A](f: IntAlg[A]): A = {
    import f._
    add(int(3), int(5))
  }

  // anamorphisms are ungood due to lack of polymorphism
  def parseExp[A](f: IntAlg[A], s: String): A = {
    import f._
    if (s matches "[0-9]+")
      int(s.toInt)
    else if (s matches """\(.*\)""")
      parseExp(f, s.tail.init)
    else
      ???
  }

  trait IntEval extends IntAlg[Int] {
    def int(x: Int): Int = x
    def add(e1: Int, e2: Int): Int = e1 + e2
  }

  trait BoolAlg[A] {
    def bool(b: Boolean): A
    def iff(e1: A, e2: A, e3: A): A
  }

  trait BoolEval extends BoolAlg[Int] {
    def bool(b: Boolean): Int = if (b) 1 else 0
    def iff(e1: Int, e2: Int, e3: Int): Int = if (e1 != 0) e2 else e3
  }

  def true3else5[A](f: IntAlg[A] with BoolAlg[A]): A = {
    import f._
    iff(bool(true), int(3), int(5))
  }
}

object TestObjectAlgebras extends ObjectAlgebras {
  def main(args: Array[String]) {
    println(s"3 + 5 = ${make3Plus5(new IntEval {})}")
    println(s"if true then 3 else 5 = ${true3else5(new IntEval with BoolEval)}")
  }
}
