import language.higherKinds

trait FunctorRep {
  trait Functor[F[_]] {
    def fmap[A, B]: (A => B) => F[A] => F[B]

    //def fix(x: F[Fix[F]]): Fix[F] = ???
  }

  type Const[X] = { type λ[Y] = X }

  type Identity[X] = X

  type Times[F[_], G[_]] = {
    type λ[X] = (F[X], G[X])
  }

  type Plus[F[_], G[_]] = {
    type λ[X] = Either[F[X], G[X]]
  }

  case class K[X]() extends Functor[Const[X]#λ] {
    def fmap[A, B] = f => identity
  }

  case object I extends Functor[Identity] {
    def fmap[A, B] = identity
  }

  case class :*:[F[_], G[_]](_1: Functor[F], _2: Functor[G])
      extends Functor[Times[F, G]#λ] {
    def fmap[A, B] = f => {
      case (x, y) => (_1.fmap(f)(x), _2.fmap(f)(y))
    }
  }

  case class :+:[F[_], G[_]](_L: Functor[F], _R: Functor[G])
      extends Functor[Plus[F, G]#λ] {
    def fmap[A, B] = f => {
      case Left(x) => Left(_L.fmap(f)(x))
      case Right(y) => Right(_R.fmap(f)(y))
    }
  }

  // F should only be a composite of sums and products
  sealed trait Fix[+F[+_]] {
    def unroll: F[Fix[F]]
    def fold[T](f: F[T] => T): T
  }

  case class Roll[+F[+_]: Functor](unroll: F[Fix[F]]) extends Fix[F] {
    def fold[T](f: F[T] => T): T = f(implicitly[Functor[F]].fmap[Fix[F], T](_.fold(f))(unroll))
  }

  object Fix {
    import language.implicitConversions

    implicit def autoUnroll[F[+_]](fixed: Fix[F]): F[Fix[F]] = fixed.unroll
  }

  // CASE STUDY: LISTS

  // hide the content of Nil because it's gonna be uninteresting
  // ... how about leaving 1 component always open for datatype a la carte?
  type ListF[+A, +L] = Either[Unit, (A, L)]

  // private[this] gets rid of unchecked variance
  private[this] type ListP[+A] = { type λ[+L] = ListF[A, L] }

  // works without @uncheckedVariance
  type List[+A] = Fix[ListP[A]#λ]

  // no, do not dream of merging fixed points any more.
  // it will be Nil() from now on, never Nil.
  object Nil {
    def apply(): List[Nothing] = Roll[ListP[Nothing]#λ](Left(())) {
      // the functor instance is annoying to write.
      // the type of a fixed-point data is even more annoying to write.
      // hide it in a macro?
      :+:[Const[Unit]#λ, Times[Const[Nothing]#λ, Identity]#λ](
        K[Unit],
        :*:[Const[Nothing]#λ, Identity](K[Nothing], I)
      )
    }
  }
}
