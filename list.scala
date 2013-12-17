trait Lists {
  trait ListF[T, L] {
    def map[M](g: L => M): ListF[T, M] = this match {
      case NilF() => NilF[T, M]()
      case ConsF(head, tail) => ConsF(head, g(tail))
    }
  }

  case class NilF[T, L] extends ListF[T, L]
  case class ConsF[T, L](head: T, tail: L) extends ListF[T, L]

  trait List[T] extends ListF[T, List[T]] {
    def fold[R](phi: ListF[T, R] => R): R = phi(this map (_ fold phi))
  }

  class Nil[T] extends NilF[T, List[T]] with List[T]

  object Nil {
    // Nil() : List[T]
    def apply[T](): List[T] = new Nil[T]

    // list match {
    //   case Nil() => ...
    // }
    def unapply[T](nil: Nil[T]): Option[Unit] = Some(())
  }

  class Cons[T](head: T, tail: List[T]) extends ConsF(head, tail) with List[T]

  object Cons {
    def apply[T](head: T, tail: List[T]): List[T] =
      new Cons(head, tail)

    def unapply[T](list: Cons[T]): Option[(T, List[T])] =
      Some((list.head, list.tail))
  }


  def sum(list: List[Int]): Int = list.fold[Int] {
    case NilF() => 0
    case ConsF(a, l) => a + l
  }

  def sum2(list: List[Int]): Int = list match {
    case Nil() => 0
    case Cons(a, restOfTheList) => a + sum2(restOfTheList)
  }
}

object TestList extends Lists {
  def main(args: Array[String]) {
    val list = Cons(1, Cons(2, Cons(3, Nil())))
    println(s"sum($list) = ${sum(list)}")
    println(s"sum2($list) = ${sum2(list)}")
  }
}
