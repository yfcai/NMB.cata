trait TypeRepresentations {
  trait Rep[A]

  case object RInt extends Rep[Int]
  case object RUnit extends Rep[Unit]

  case class RProd[A, B](ra: Rep[A], rb: Rep[B]) extends Rep[(A, B)]
  case class RPlus[A, B](ra: Rep[A], rb: Rep[B]) extends Rep[Either[A, B]]

  trait Unroll[A, B] extends Rep[A] { def unroll: A => (B, Rep[B]) }

  type ListF[A, L] = Either[Unit, (A, L)]

  def repListF[A, L](ra: Rep[A], rl: Rep[L]): Rep[ListF[A, L]] = RPlus(RUnit, RProd(ra, rl))

  class RepList[A](ra: Rep[A]) extends Unroll[List[A], ListF[A, List[A]]] {
    def unroll = {
      case Nil => (Left(()), repListF(ra, this)) // tie the knot with `this`
      case x :: xs => (Right((x, xs)), repListF(ra, this))
    }
  }

  // strange thing:
  // if pattern matching on `rep` isn't complete,
  // then stack overflow instead of match error... why?
  def sumAllInts[T](x: T)(rep: Rep[T]): Int = rep match {
    case RUnit => 0 // if this is left out, then stack overflow
    case RInt => x
    case RProd(ra, rb) => sumAllInts(x._1)(ra) + sumAllInts(x._2)(rb)
    case RPlus(ra, rb) => x.fold(a => sumAllInts(a)(ra), b => sumAllInts(b)(rb))
    case r: Unroll[_, _] => r unroll x match { case (b, rb) => sumAllInts(b)(rb) }
  }

  // remaining questions
  //
  // 1. is there any way to have ADT carry their own type rep,
  //    such that traversals need only take 1 type parameter?
  //
  // 2. every n-hole contexts of an ADT defines a functor.
  //    every functor defines a map (commuting) function
  //    is there any way to support all the map functions?
  //    if there is, then we can also support replacing type
  //    annotations in a term.
}

object TestTypeRepresentations extends TypeRepresentations {
  def main(args: Array[String]) {

    val xs = (1 to 100).toList

    val sumXs: Int = sumAllInts(xs)(new RepList(RInt))

    println(s"sum(1..100) = $sumXs")
  }
}
