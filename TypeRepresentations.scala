import language.implicitConversions

trait TypeRepresentations {
  trait Rep[A]

  implicit case object RInt extends Rep[Int]

  case class RProd[A, B](ra: Rep[A], rb: Rep[B]) extends Rep[(A, B)]
  case class RPlus[A, B](ra: Rep[A], rb: Rep[B]) extends Rep[Either[A, B]]
  case class RView[A, B](iso: Iso[A, B], r: () => Rep[A]) extends Rep[B]

  implicit def rProd[A, B](implicit ra: Rep[A], rb: Rep[B]): Rep[(A, B)] = RProd(ra, rb)
  implicit def rPlus[A, B](implicit ra: Rep[A], rb: Rep[B]): Rep[Either[A, B]] = RPlus(ra, rb)
  implicit def rView[A, B](implicit iso: Iso[A, B], r: () => Rep[A]): Rep[B] = RView(iso, r)

  trait Iso[A, B] { def from: A => B ; def to: B => A }
  case class KIso[A, B](from: A => B, to: B => A) extends Iso[A, B]

  //implicit def commuteIso[A, B](iso: Iso[B, A]): Iso[A, B] = KIso(iso.to, iso.from)

  type ListF[A, L] = Either[Unit, (A, L)]

  def isoListF[A]: Iso[List[A], ListF[A, List[A]]] = KIso({
    case Nil => Left(())
    case x :: xs => Right((x, xs))
  }, {
    case Left(()) => Nil
    case Right((x, xs)) => x :: xs
  })

  // does not help... neither does commuteIso: Iso[A, B] => Iso[B, A].
  implicit def isoListF2[A]: Iso[ListF[A, List[A]], List[A]] = {
    val iso = isoListF[A]
    KIso(iso.to, iso.from)
  }

  implicit def thunkifyRep[A](r: => Rep[A]): () => Rep[A] = () => r

  def sumAllInts[T](x: T)(implicit r: Rep[T]): Int = r match {
    case RInt => x
    case RProd(ra, rb) => sumAllInts(x._1)(ra) + sumAllInts(x._2)(rb)
    case RPlus(ra, rb) => x.fold(a => sumAllInts(a)(ra), b => sumAllInts(b)(rb))
    case RView(iso, r) => sumAllInts(iso to x)(r())
  }
}

object TestTypeRepresentations extends TypeRepresentations { def main(args: Array[String]) {
  val xs = (1 to 100).toList
  // problem: diverging implicit expansion
  val sumXs: Int =
    // sumAllInts(xs) // could not find implicit value r: Rep[List[Int]]
    // sumAllInts(xs)(rView) // could not find implicit value r: () => Rep[A]
    // sumAllInts(xs)(rView(isoListF2, () => rPlus)) // diverging implicit expansion
    ???

  // type rep may be useful in haskell. in scala, runtime instanceOf tests work better.
}}
