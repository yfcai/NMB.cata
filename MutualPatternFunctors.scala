import language.higherKinds

trait MutualPatternFunctors {
  // pattern functor
  trait Functor[F[_]] {
    def fmap[A, B](f: A => B)(fa: F[A]): F[B]
  }

  sealed trait EvenF[+_]
  case object ZeroF extends EvenF[Nothing]
  case class EsucF[T](pred: T) extends EvenF[T]

  sealed trait OddF[+_]
  case class OsucF[T](pred: T) extends OddF[T]

  implicit object evenPatternFunctor extends Functor[EvenF] {
    def fmap[A, B](f: A => B)(ea: EvenF[A]): EvenF[B] = ea match {
      case ZeroF => ZeroF
      case EsucF(pred) => EsucF(f(pred))
    }
  }

  implicit object oddPatternFunctor extends Functor[OddF] {
    def fmap[A, B](f: A => B)(oa: OddF[A]): OddF[B] = oa match {
      case OsucF(pred) => OsucF(f(pred))
    }
  }

  // recursive data level 0
  // (has to come after the functor instance declarations)
  sealed trait Even {
    def unroll: EvenF[Odd]
    def unroll1: EvenF1[Even]

    def fold[A](f: EvenF1[A] => A): A = f(unroll1 map (_ fold f))
  }

  case object Zero extends Even {
    def unroll: EvenF[Odd] = ZeroF
    def unroll1: EvenF1[Even] = ZeroF1
  }

  case class Esuc(pred: Odd) extends Even {
    def unroll: EvenF[Odd] = EsucF(pred)
    def unroll1: EvenF1[Even] = EsucF1(pred.unroll)
  }

  sealed trait Odd {
    def unroll: OddF[Even]
    def unroll1: OddF1[Odd]

    def fold[A](f: OddF1[A] => A): A = f(unroll1 map (_ fold f))
  }

  case class Osuc(pred: Even) extends Odd {
    def unroll: OddF[Even] = OsucF(pred)
    def unroll1: OddF1[Odd] = OsucF1(pred.unroll)
  }

  // recursive data level 1
  sealed trait Even1
  case object Zero1 extends Even1
  case class Esuc1(pred: OddF[Even1]) extends Even1

  sealed trait Odd1
  case class Osuc1(pred: EvenF[Odd1]) extends Odd1

  def unroll1(e: Even1): EvenF[OddF[Even1]] = e match {
    case Zero1 => ZeroF
    case Esuc1(pred) => EsucF(pred)
  }

  def unroll1(o: Odd1): OddF[EvenF[Odd1]] = o match {
    case Osuc1(pred) => OsucF(pred)
  }

  // pattern functor level 1
  sealed trait EvenF1[+A] {
    def map[B](f: A => B)(implicit fi: Functor[OddF]): EvenF1[B]
  }

  case object ZeroF1 extends EvenF1[Nothing] {
    def map[B](f: Nothing => B)(implicit fi: Functor[OddF]): EvenF1[B] = ZeroF1
  }

  case class EsucF1[A](pred: OddF[A]) extends EvenF1[A] {
    def map[B](f: A => B)(implicit fi: Functor[OddF]): EvenF1[B] = EsucF1(fi.fmap(f)(pred))
  }

  sealed trait OddF1[+A] {
    def map[B](f: A => B)(implicit fi: Functor[EvenF]): OddF1[B]
  }

  case class OsucF1[A](pred: EvenF[A]) extends OddF1[A] {
    def map[B](f: A => B)(implicit fi: Functor[EvenF]): OddF1[B] = OsucF1(fi.fmap(f)(pred))
  }
}

object TestMutualPatternFunctors extends MutualPatternFunctors {

  def toInt(e: Even): Int = e.fold[Int] {
    case ZeroF1 => 0
    case EsucF1(OsucF(precedingEvenNumber)) => precedingEvenNumber + 2
  }

  def toInt(o: Odd): Int = o.fold[Int] {
    case OsucF1(ZeroF) => 1
    case OsucF1(EsucF(precedingOddNumber)) => precedingOddNumber + 2
  }

  def main(args: Array[String]) {
    val evenNumberSix: Even = Esuc(Osuc(Esuc(Osuc(Esuc(Osuc(Zero))))))
    val oddNumberSeven: Odd = Osuc(evenNumberSix)

    println(s"toInt(evenNumberSix)  = ${toInt(evenNumberSix)}")
    println(s"toInt(oddNumberSeven) = ${toInt(oddNumberSeven)}")
  }
}
