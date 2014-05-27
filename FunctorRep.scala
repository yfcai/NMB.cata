import language.higherKinds

trait FunctorRep {
  trait Functor[F[_]] {
    def fmap[A, B]: (A => B) => F[A] => F[B]

    // this method is impossible short of making every functor covariant
    // which also makes functor instances untypeable
    // sample error messsage: [+X](Nothing, X) expected, [X](Nothing, X) encountered
    //
    //def fix(x: G[Fix[G]]): Fix[G] = ???
  }

  type Const[X] = { type λ[Y] = X }

  type Identity[X] = X

  case class P[+A, +B](_1: A, _2: B)
  sealed trait S[+A, +B]
  case class L[+A](get: A) extends S[A, Nothing]
  case class R[+B](get: B) extends S[Nothing, B]

  type LP[F[_], G[_]] = {
    type λ[X] = P[F[X], G[X]]
  }

  type LS[F[_], G[_]] = {
    type λ[X] = S[F[X], G[X]]
  }

  case class K[X]() extends Functor[Const[X]#λ] {
    def fmap[A, B] = f => identity
  }

  case object I extends Functor[Identity] {
    def fmap[A, B] = identity
  }

  case class :*:[F[_], G[_]](_1: Functor[F], _2: Functor[G])
      extends Functor[LP[F, G]#λ] {
    def fmap[A, B] = f => {
      case P(x, y) => P(_1.fmap(f)(x), _2.fmap(f)(y))
    }
  }

  case class :+:[F[_], G[_]](_L: Functor[F], _R: Functor[G])
      extends Functor[LS[F, G]#λ] {
    def fmap[A, B] = f => {
      case L(x) => L(_L.fmap(f)(x))
      case R(y) => R(_R.fmap(f)(y))
    }
  }

  sealed trait Fix[+F[+_]] {
    this: F[Fix[F]] =>
    import annotation.unchecked.uncheckedVariance
    // this.functor is write-only, do not call it elsewhere!
    val functor: Functor[F] @uncheckedVariance
    def fold[T](f: F[T] => T): T = f(functor.fmap[Fix[F], T](_.fold(f))(this))
  }

  // CASE STUDY: LISTS

  // can't call List.PatternFunctor[A]#λ here
  // so that variance is checked
  type List[+A] = Fix[({ type λ[+L] = S[Unit, P[A, L]] })#λ]

  object List {
    type F[A] = { type λ[+L] = S[Unit, P[A, L]] }

    def patternFunctor[A]: Functor[F[A]#λ] =
      // the functor instance is annoying to write.
      //
      // TODO
      // 1. def macro to fill in type annotations.
      // 2. def macro to convert nominal syntax & mutual recursions into this
      :+:[Const[Unit]#λ, LP[Const[A]#λ, Identity]#λ](
        K[Unit],
        :*:[Const[A]#λ, Identity](K[A], I))
  }

  // no, do not dream of merging fixed points any more.
  // it will be Nil() from now on, never Nil.
  object Nil {
    def apply(): List[Nothing] =
      new L(()) with Fix[List.F[Nothing]#λ] {
        val functor = List.patternFunctor
      }

    /*
    def unapply(xs: Either[_, _]): Boolean = xs match {
      // each case matches both the fixed point and the pattern...
      case Left(()) => true
      case _ => false
    } */
  }
/*
  object Cons {
    def apply[A](x: A, xs: List[A]): List[A] =
      ??? //Roll[List.PatternFunctor[A]#λ](Right((x, xs)))(List.patternFunctor)

    def unapply[A](xs: Either[_, (A, List[A])]): Option[(A, List[A])] =
      xs match {
        case Right((x, xs)) => Some((x, xs))
        case _ => None
      }
  }*/
}

object TestFunctorRep extends FunctorRep {
/*
  val xs: List[Int] = Nil()

  def main(args: Array[String]) {
    // xs match { case Nil() => println("ok") } // uncaught MatchError
    xs match {
      case Nil() => println("ok")
    }
  }*/
}
