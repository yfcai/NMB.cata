import language.higherKinds

trait FunctorRep {
  // functors are strictly positive
  trait Functor[F[+_]] {
    def fmap[A, B]: (A => B) => F[A] => F[B]
  }

  type Const[X] = { type λ[+Y] = X }

  type Identity[+X] = X

  case class P[+A, +B](_1: A, _2: B)
  sealed trait S[+A, +B]
  case class L[+A](get: A) extends S[A, Nothing]
  case class R[+B](get: B) extends S[Nothing, B]

  type LP[F[+_], G[+_]] = {
    type λ[+X] = P[F[X], G[X]]
  }

  type LS[F[+_], G[+_]] = {
    type λ[+X] = S[F[X], G[X]]
  }

  case class K[X]() extends Functor[Const[X]#λ] {
    def fmap[A, B] = f => identity
  }

  case object I extends Functor[Identity] {
    def fmap[A, B] = identity
  }

  case class :*:[F[+_], G[+_]](_1: Functor[F], _2: Functor[G])
      extends Functor[LP[F, G]#λ] {
    def fmap[A, B] = f => {
      case P(x, y) => P(_1.fmap(f)(x), _2.fmap(f)(y))
    }
  }

  case class :+:[F[+_], G[+_]](_L: Functor[F], _R: Functor[G])
      extends Functor[LS[F, G]#λ] {
    def fmap[A, B] = f => {
      case L(x) => L(_L.fmap(f)(x))
      case R(y) => R(_R.fmap(f)(y))
    }
  }

  sealed trait Fix[+F[+_]] {
    this: F[Fix[F]] =>
    import annotation.unchecked.uncheckedVariance
    val functor: Functor[F] @uncheckedVariance // will it lead to soundness problems?
    def fold[T](f: F[T] => T): T = f(functor.fmap[Fix[F], T](_.fold(f))(this))
  }

  // fixed point of a bifunctor is a functor
  // TODO: attempt more than 2 levels of recursion.
  //       will it require another trait, or will Mu be fine?
  trait Mu[H[+X, +R]] extends Functor[({ type λ[+X] = Fix[({ type λ[+R] = H[X, R] })#λ] })#λ] {
    // ΛX. H[X, R] is a functor for all R.
    def functor[R]: Functor[({ type λ[+X] = H[X, R] })#λ]

    private[this] type Fixed[+X] = Fix[({ type λ[+R] = H[X, R] })#λ]

    def fmap[A, B](f: A => B): Fixed[A] => Fixed[B] = fixedA => {
      val fun = functor[Fixed[B]]
      fixedA.fold[Fixed[B]](a_bs => {
        val unrolled: H[B, Fixed[B]] = fun.fmap(f)(a_bs)
        ??? : Fixed[B]
        // the conversion from H[B, Fixed[B]] to Fixed[B] is impossible.
        // TODO: consent to manual unrolling. there is no other way.
      })
    }
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
      // lack of manual unrolling is good,
      // but it makes it rather hard to roll unknown things.
      new L(()) with Fix[List.F[Nothing]#λ] {
        val functor = List.patternFunctor[Nothing]
      }

    def unapply(xs: S[Unit, P[_, _]]): Boolean = xs match {
      // each case matches both the fixed point and the pattern...
      case L(()) => true
      case _ => false
    }
  }

  object Cons {
    def apply[A](x: A, xs: List[A]): List[A] =
      new R(P(x, xs)) with Fix[List.F[A]#λ] {
        val functor = List.patternFunctor[A]
      }

    def unapply[A, L](xs: S[Unit, P[A, L]]): Option[(A, L)] =
      xs match {
        case R(P(x, xs)) => Some((x, xs))
        case _ => None
      }
  }

  // CASE STUDY: EVEN/ODD

  type EvenF[+O] = S[Unit, O]
  type OddF[+E] = P[Unit, E]
}

object TestFunctorRep extends FunctorRep {
  val xs: List[Int] = Cons(1, Cons(2, Cons(3, Cons(4, Nil()))))

  def main(args: Array[String]) {
    val sum = xs.fold[Int] {
      case Nil() => 0
      case Cons(x, xs) => x + xs
    }
    println(s"xs = $xs")
    println(s"sum(xs) = $sum")
  }
}
