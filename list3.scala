/** Functors with transparent rolling & unrolling
  * (requires manual recreation of case-class overrides)
  *
  * Advantages
  * - no namespace pollution
  * - to those who don't care, ListF may as well not exist
  *
  * Disadvantage
  * - "Cons" is not a case class any more & can't take
  *   advantage of scala's special treatment of case classes
  */

import scala.language.implicitConversions

trait List3 {
  trait ListF[+T, +L] {
    def map[M](f: L => M): ListF[T, M]
  }

  trait List[+T] extends ListF[T, List[T]] {
    def fold[R](f: ListF[T, R] => R): R =
      f(map(_ fold f))

    def foldByName[R](f: (=> ListF[T, R]) => R): R =
      f(map(_ foldByName f))
  }

  case object Nil extends ListF[Nothing, Nothing] with List[Nothing] {
    def map[M](f: Nothing => M): ListF[Nothing, M] = this
  }

  class Cons[+T, +L](val head: T, val tail: L) extends ListF[T, L] {
    // obligation: ListF
    def map[M](f: L => M): ListF[T, M] = new Cons(head, f(tail))

    // override methods as if a case class

    override def toString: String = s"Cons($head, $tail)"

    override def equals(that: Any) = that match {
      case c: Cons[T, L] => c.head == head && c.tail == tail
      case _ => false
    }

    override def hashCode: Int = rehash(head.hashCode, tail.hashCode)

    // stupidest hash function
    def rehash(lhs: Int, rhs: Int): Int = lhs + rhs
  }

  object Cons {
    // transparent rolling
    private class FixedCons[+T](head: T, tail: List[T])
        extends Cons(head, tail) with List[T]

    def apply[T](head: T, tail: List[T]): List[T] =
      new FixedCons(head, tail)

    def unapply[T, L](listF: ListF[T, L]): Option[(T, L)] = listF match {
      case c: Cons[T, L] => Some((c.head, c.tail))
      case _ => None
    }
  }
}

object TestList3 extends List3 {
  def sum(list: List[Int]): Int = list.fold[Int] {
    case Nil => 0
    case Cons(n, m) => n + m
  }

  def sum2(list: List[Int]): Int = list match {
    case Nil => 0
    case Cons(n, tail) => n + sum2(tail)
  }

  val list = (1 to 10).foldRight[List[Int]](Nil)((x, xs) => Cons(x, xs))

  def main(args: Array[String]) {
    println(list)
    println(s" sum(list) = ${sum(list)}")
    println(s"sum2(list) = ${sum2(list)}")
  }
}
