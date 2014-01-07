// Example showcasing covariant type parameters

object Functors {
  trait ListF[+A, +T] {
    def map[R](f: T => R): ListF[A, R] = this match {
      case Nil => Nil
      case ConsF(x, xs) => ConsF(x, f(xs))
    }
  }

  trait List[+A] extends ListF[A, List[A]] {
    def fold[T](f: ListF[A, T] => T): T = f(this.map(_.fold(f)))
  }

  case object Nil extends ListF[Nothing, Nothing] with List[Nothing]
  case class ConsF[+A, +T](x: A, xs: T) extends ListF[A, T]

  class Cons[+A](x: A, xs: List[A]) extends ConsF(x, xs) with List[A] {
    override def toString = s"Cons($x, $xs)"
  }

  object Cons {
    def apply[A](x: A, xs: List[A]): List[A] = new Cons(x, xs)
    def unapply[A, T](xs: ListF[A, T]): Option[(A, T)] = xs match {
      case ConsF(x, xs) => Some((x, xs))
      case _ => None
    }
  }
  // this helps when people write list @ Cons(x, xs)...
  // not completely; just a little bit.
  import scala.language.implicitConversions
  implicit def fixedPointOfListF[A](x: ListF[A, List[A]]): List[A] =
    x match {
      case Nil => Nil
      case ConsF(x, xs) => new Cons(x, xs)
    }

  def man[T: Manifest](x: T) = manifest[T]

  def main(args: Array[String]) {
    val x = Cons(1, Cons(2, Cons(3, Cons(4, Nil))))
    println(man(x))
    println(x)

    val sum = x.fold[Int] {
      case Nil => 0
      case Cons(x, xs) => x + xs
    }

    println(s"sum = $sum")
  }
}
