trait FunctorRep {
  import language.higherKinds

  case class :*:[+A, +B](_1: A, _2: B)

  sealed trait :+:[+A, +B]
  case class L[+A](get: A) extends (A :+: Nothing)
  case class R[+B](get: B) extends (Nothing :+: B)

  implicit class makeProductSum[B](b: B) {
    def :*:[A](a: A) = new :*:(a, b)
  }

  trait Functor[F[_]] {
    def fmap[A, B]: (A => B) => F[A] => F[B]
  }

  type ConstantFunctor[X] = { type λ[Y] = X }

  type IdentityFunctor[X] = X

  type ProductFunctor[F[_], G[_]] = {
    type λ[X] = F[X] :*: G[X]
  }

  type SumFunctor[F[_], G[_]] = {
    type λ[X] = F[X] :+: G[X]
  }

  case class K[X]() extends Functor[ConstantFunctor[X]#λ] {
    def fmap[A, B] = f => identity
  }

  case object I extends Functor[IdentityFunctor] {
    def fmap[A, B] = identity
  }

  case class |*|[F[_], G[_]](_1: Functor[F], _2: Functor[G])
      extends Functor[ProductFunctor[F, G]#λ] {
    def fmap[A, B] = f => {
      case x :*: y => _1.fmap(f)(x) :*: _2.fmap(f)(y)
    }
  }

  case class |+|[F[_], G[_]](_L: Functor[F], _R: Functor[G])
      extends Functor[SumFunctor[F, G]#λ] {
    def fmap[A, B] = f => {
      case L(x) => L(_L.fmap(f)(x))
      case R(y) => R(_R.fmap(f)(y))
    }
  }

  implicit class mkFunctor[F[_]](_f: Functor[F]) {
    def |*|[G[_]](_g: Functor[G]) = new |*|(_f, _g)
    def |+|[G[_]](_g: Functor[G]) = new |+|(_f, _g)
  }
}

trait ListFunctorRep extends FunctorRep {
  type ListF[+A, +L] = Unit :+: (A :*: L)
  sealed trait List[+A] extends ListF[A, List[A]] {
    def fold[T](f: ListF[A, T] => T): T = {
      val kki = functorKKI[Unit, A]
      def loop(x: List[A]): T = f(kki.fmap(loop)(x))
      loop(this)
    }

    def map[B](f: A => B): List[B] = {
      val kik = functorKIK[Unit, List[B]]
      fold[List[B]](a_bs => kik.fmap(f)(a_bs))
    }

    def toStandardList = fold[collection.immutable.List[A]] {
      case L(()) => Nil
      case R(x :*: xs) => x :: xs
    }

    override def toString = toStandardList.toString

    private[this] def functorKKI[T1, T2] =
      // hopefully scala 2.11 relieves the excessive type annotation.
      // otherwise this is really horrible.
      |+|[
        ConstantFunctor[T1]#λ,
        ProductFunctor[ConstantFunctor[T2]#λ, IdentityFunctor]#λ
      ](K[T1], |*|[ConstantFunctor[T2]#λ, IdentityFunctor](K[T2], I))

    private[this] def functorKIK[T1, T3] =
      |+|[
        ConstantFunctor[T1]#λ,
        ProductFunctor[IdentityFunctor, ConstantFunctor[T3]#λ]#λ
      ](K[T1], |*|[IdentityFunctor, ConstantFunctor[T3]#λ](I, K[T3]))
  }

  object List {
    import language.implicitConversions

    implicit def fixListF[A](xs: ListF[A, List[A]]): List[A] = xs match {
      case L(()) => new L(()) with List[A]
      case R(xs) => new R(xs) with List[A]
    }

    def apply[A](args: A*): List[A] =
      args.foldRight[List[A]](L(()))((x, xs) => R(x :*: xs))
  }
}

trait NominalListFunctorRep extends FunctorRep {
  // like ListFunctorRep, but with named functor builders
}

object TestFunctorRep extends ListFunctorRep with NominalListFunctorRep {
  val xs = List(1, 2, 3, 4, 5)

  def main(args: Array[String]) {
    val fac5 = xs.fold[Int] {
      case L(()) => 1
      case R(m :*: n) => m * n
    }
    println(s"Π $xs = $fac5")
    println(s"7 .* xs = ${xs map (_ * 7)}")
  }
}
