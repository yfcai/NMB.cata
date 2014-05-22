import language.higherKinds

trait FunctorRep {
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

  type Const[X] = { type λ[Y] = X }

  type Identity[X] = X

  type Times[F[_], G[_]] = {
    type λ[X] = F[X] :*: G[X]
  }

  type Plus[F[_], G[_]] = {
    type λ[X] = F[X] :+: G[X]
  }

  case class K[X]() extends Functor[Const[X]#λ] {
    def fmap[A, B] = f => identity
  }

  case object I extends Functor[Identity] {
    def fmap[A, B] = identity
  }

  case class |*|[F[_], G[_]](_1: Functor[F], _2: Functor[G])
      extends Functor[Times[F, G]#λ] {
    def fmap[A, B] = f => {
      case x :*: y => _1.fmap(f)(x) :*: _2.fmap(f)(y)
    }
  }

  case class |+|[F[_], G[_]](_L: Functor[F], _R: Functor[G])
      extends Functor[Plus[F, G]#λ] {
    def fmap[A, B] = f => {
      case L(x) => L(_L.fmap(f)(x))
      case R(y) => R(_R.fmap(f)(y))
    }
  }

  implicit class mkFunctor[F[_]](_f: Functor[F]) {
    def |*|[G[_]](_g: Functor[G]) = new |*|(_f, _g)
    def |+|[G[_]](_g: Functor[G]) = new |+|(_f, _g)
  }

  // alternative to making your own fixed point: the Roll.
  sealed trait Fix[F[_]] {
    def unroll: F[Fix[F]]
    def fold[T](f: F[T] => T): T
  }

  case class Roll[F[_]: Functor](unroll: F[Fix[F]]) extends Fix[F] {
    def fold[T](f: F[T] => T): T = f(implicitly[Functor[F]].fmap[Fix[F], T](_.fold(f))(unroll))
  }
}

trait GenericListFunctorRep extends FunctorRep {
  type GListF[+U, +A, +L] = U :+: (A :*: L)
  type GListP[+A, +L] = GListF[Unit, A, L]
  sealed trait GList[+A] extends GListP[A, GList[A]] {
    def fold[T](f: GListP[A, T] => T): T = {
      val kki = functorKKI[Unit, A]
      def loop(x: GList[A]): T = f(kki.fmap(loop)(x))
      loop(this)
    }

    def map[B](f: A => B): GList[B] = {
      val kik = functorKIK[Unit, GList[B]]
      fold[GList[B]](a_bs => kik.fmap(f)(a_bs))
    }

    def toStandardList = fold[collection.immutable.List[A]] {
      case L(()) => Nil
      case R(x :*: xs) => x :: xs
    }

    override def toString = s"GList(s${toStandardList.mkString(", ")})"

    private[this] def functorKKI[T1, T2] =
      // scala 2.11 does not relieve the excessive type annotation.
      // looks like we gotta resort to def macros...
      |+|[
        Const[T1]#λ,
        Times[Const[T2]#λ, Identity]#λ
      ](K[T1], |*|[Const[T2]#λ, Identity](K[T2], I))

    private[this] def functorKIK[T1, T3] =
      |+|[
        Const[T1]#λ,
        Times[Identity, Const[T3]#λ]#λ
      ](K[T1], |*|[Identity, Const[T3]#λ](I, K[T3]))
  }

  object GNil extends L(()) with GList[Nothing] {
    // in lieu of unapply(), to act like a case object without being one
    override def equals(that: Any): Boolean = that match {
      case L(()) => true
      case _ => false
    }
  }

  object GCons {
    def apply[A](x: A, xs: GList[A]): GList[A] = R(x :*: xs)
    def unapply[A, B, C](xs: GListF[A, B, C]): Option[(B, C)] = xs match {
      case R(x :*: xs) => Some((x, xs))
      case _ => None
    }
  }

  object GList {
    import language.implicitConversions

    // implicit conversion has to be there.
    // mixed-in fixed point unrolls automatically.
    // rolling can't be transparent, though.
    implicit def fixGListP[A](xs: GListP[A, GList[A]]): GList[A] = xs match {
      case L(()) => new L(()) with GList[A]
      case R(xs) => new R(xs) with GList[A]
    }

    def apply[A](args: A*): GList[A] = args.foldRight[GList[A]](GNil)(GCons[A])
  }
}

trait NominalListFunctorRep extends FunctorRep {
  sealed trait NListF[+A, +B, +C]
  case class NNil[+A](get: A) extends NListF[A, Nothing, Nothing]
  case class NCons[+B, +C](head: B, tail: C) extends NListF[Nothing, B, C]

  type NListP[A] = {
    type λ[L] = NListF[Unit, A, L]
  }

  // here shows disadvantage of manual rolling:
  // there's no way to have List[Set] be a subtype of List[Iterable],
  // because RHS of inner type NListPatternFunctor#λ is an invariant
  // position.

  // also, functors have to be implicit.

  // also, can't tailor-make reasonable map functions in fixed points,
  // because the type of `map` depends on some functor that's not
  // the pattern functor.

  // since we need macros anyway, generated fixed points feel better.

  // So, issues of contension:
  // 1. roll+unroll, or new Functor(stuff) with FixedPoint?
  // 2. KISP, or nominal functor instances?

  type NList[A] = Fix[NListP[A]#λ]

  type NListC[A[_], B[_], C[_]] = {
    type λ[X] = NListF[A[X], B[X], C[X]]
  }

  case class NListFun[A[_], B[_], C[_]](nil: Functor[A], head: Functor[B], tail: Functor[C])
      extends Functor[NListC[A, B, C]#λ] {
    def fmap[X, Y] = f => {
      case NNil(a) => NNil(nil.fmap(f)(a))
      case NCons(x, xs) => NCons(head.fmap(f)(x), tail.fmap(f)(xs))
    }
  }

  type NListKIM[B[_]] = { type λ[X] = NList[B[X]] }

  object NList {
    import language.implicitConversions
    implicit def fixNListP[A, L <% NList[A]](xs: NListF[Unit, A, L]): NList[A] = xs match {
      case NNil(()) =>
        Roll[NListP[A]#λ](NNil(()))

      case NCons(head, tail) =>
        Roll[NListP[A]#λ](NCons(head, tail /* recursive implicit conversion here */))
    }

    implicit def kki[A]: Functor[NListP[A]#λ] = // NListFun(K[Unit], K[A], I) // does not help...
      NListFun[Const[Unit]#λ, Const[A]#λ, Identity](K[Unit], K[A], I)

    def kik[C]: Functor[NListC[Const[Unit]#λ, Identity, Const[C]#λ]#λ] =
      NListFun[Const[Unit]#λ, Identity, Const[C]#λ](K[Unit], I, K[C])

    def kim: Functor[NListKIM[Identity]#λ] = new Functor[NListKIM[Identity]#λ] {
      def fmap[X, Y] = {
        val fun = kik[NList[Y]]
        f => _.fold[NList[Y]](ys => fun.fmap(f)(ys) /* implicit conversion here */)
      }
    }

    def apply[A](ys: A*): NList[A] = ys.foldRight[NList[A]](NNil(()))((x, xs) => NCons(x, xs))
  }

  implicit class MappableNList[A](xs: NList[A]) {
    def map[B](f: A => B): NList[B] = NList.kim.fmap(f)(xs)

    def toStandardList: List[A] = xs.fold[List[A]] {
      case NNil(()) => Nil
      case NCons(head, tail) => head :: tail
    }

    def pretty: String = s"NList(${toStandardList.mkString(", ")})"
  }
}

object TestFunctorRep extends GenericListFunctorRep with NominalListFunctorRep {
  val xs = GList(1, 2, 3, 4, 5)

  val ys = NList(1, 2, 3, 4, 5)

  def main(args: Array[String]) {
    val fac5 = xs.fold[Int] {
      case GNil => 1
      case GCons(m, n) => m * n
    }
    println(s"Π $xs = $fac5")
    println(s"7 .* xs = ${xs map (_ * 7)}")

    println()

    val nfac5 = ys.fold[Int]({
      case NNil(()) => 1
      case NCons(m, n) => m * n
    })
    println(s"Π ${ys.pretty} = $nfac5")
    println(s"7 .* ys = ${ys.map(_ * 7).pretty}")

    println()

    GList() match {
      case GNil => println("GList() matches GNil.")
    }
  }
}
