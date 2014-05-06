import annotation.unchecked.uncheckedVariance
import language.higherKinds

trait FCategories {
  trait Functor[F[_]] {
    def fmap[A, B](f: A => B): F[A] => F[B]
  }

  sealed abstract class Fix[F[_]: Functor] {
    def unroll: F[Fix[F]]

    // the unique morphism β to make the following diagram commute:
    //
    // F[Fix[F]]  --[Roll]-->  Fix[F]
    //
    //     |                     |
    //     | fmap(β)           β |
    //     V                     V
    //
    //    F[B]   -----[f]---->   B
    //
    def fold[B](f: F[B] => B): Fix[F] => B =
      x => f( implicitly[Functor[F]].fmap(fold(f))(x.unroll) )
  }

  case class Roll[F[_]: Functor](unroll: F[Fix[F]]) extends Fix[F]

  implicit class Mappable[F[_], A](x: F[A]) {
    def map[B](f: A => B)(implicit fi: Functor[F]): F[B] = fi.fmap(f)(x)
  }

  case class :*:[+A, +B](_1: A, _2: B)
  implicit class ProductConstructor[B](b: B) {
    def :*:[A](a: A): (A :*: B) = new :*:(a, b)
  }

  sealed trait :+:[+A, +B]
  case class L[+A](a: A) extends :+:[A, Nothing]
  case class R[+B](b: B) extends :+:[Nothing, B]

  type I[T] = T
  type Curry[F[_, _]] = { type λ[A] = { type λ[B] = F[A, B] } }
  type Flip[F[_, _]] = { type λ[A, B] = F[B, A] }

  type Prod1[F[_], B   ] = { type λ[A] = F[A] :*: I[B] }
  type Prod2[A   , F[_]] = { type λ[B] = I[A] :*: F[B] }
  type Prod3[F[_], G[_]] = { type λ[A] = F[A] :*: G[A] }
  type Plus1[F[_], B   ] = { type λ[A] = F[A] :+: I[B] }
  type Plus2[A   , F[_]] = { type λ[B] = I[A] :+: F[B] }
  type Plus3[F[_], G[_]] = { type λ[A] = F[A] :+: G[A] }


  implicit object IdentityFunctor extends Functor[I] {
    def fmap[A, B](f: A => B): A => B = f
  }

  // a bifunctor trait will reduce boilerplates in prod1, prod2 etc.

  def prod1[F[_]: Functor, B]: Functor[Prod1[F, B]#λ] = new Functor[Prod1[F, B]#λ] {
    def fmap[A1, A2](f: A1 => A2): (F[A1] :*: B) => (F[A2] :*: B) = {
      case x :*: y => implicitly[Functor[F]].fmap(f)(x) :*: y
    }
  }

  def prod2[A, G[_]: Functor]: Functor[Prod2[A, G]#λ] = new Functor[Prod2[A, G]#λ] {
    def fmap[B1, B2](f: B1 => B2): (A :*: G[B1]) => (A :*: G[B2]) = {
      case x :*: y => x :*: implicitly[Functor[G]].fmap(f)(y)
    }
  }

  def prod3[F[_]: Functor, G[_]: Functor]: Functor[Prod3[F, G]#λ] = new Functor[Prod3[F, G]#λ] {
    def fmap[A, B](f: A => B): (F[A] :*: G[A]) => (F[B] :*: G[B]) = {
      case x :*: y => implicitly[Functor[F]].fmap(f)(x) :*: implicitly[Functor[G]].fmap(f)(y)
    }
  }

  def plus1[F[_]: Functor, B]: Functor[Plus1[F, B]#λ] = new Functor[Plus1[F, B]#λ] {
    def fmap[A1, A2](f: A1 => A2): (F[A1] :+: B) => (F[A2] :+: B) = {
      case L(x) => L(implicitly[Functor[F]].fmap(f)(x))
      case R(y) => R(y)
    }
  }

  def plus2[A, G[_]: Functor]: Functor[Plus2[A, G]#λ] = new Functor[Plus2[A, G]#λ] {
    def fmap[B1, B2](f: B1 => B2): (A :+: G[B1]) => (A :+: G[B2]) = {
      case L(x) => L(x)
      case R(y) => R(implicitly[Functor[G]].fmap(f)(y))
    }
  }

  def plus3[F[_]: Functor, G[_]: Functor]: Functor[Plus3[F, G]#λ] = new Functor[Plus3[F, G]#λ] {
    def fmap[A, B](f: A => B): (F[A] :+: G[A]) => (F[B] :+: G[B]) = {
      case L(x) => L(implicitly[Functor[F]].fmap(f)(x))
      case R(y) => R(implicitly[Functor[G]].fmap(f)(y))
    }
  }

  type Fix2[F[_, _]] = { type λ[A] = Fix[Curry[F]#λ[A]#λ] }

  // need bifunctor somewhere maybe?
  def fix2[F[_, _]]: Functor[Fix2[F]#λ] = new Functor[Fix2[F]#λ] {
    private[this] type G[A] = Curry[F]#λ[A]
    def fmap[A, B](f: A => B): Fix[G[A]#λ] => Fix[G[B]#λ] =
      ???
      //_.fold[Fix[G[B]#λ]](??? : Fix2[F]#λ[Fix[G[B]#λ]] => Fix[G[B]#λ])

      //  ((y: Fix2[F]#λ[Fix[G[B]#λ]]) =>
      //    ??? : Fix[G[B]#λ])(??? : Functor[ ])
  }

  type ListF[+A, +L] = Unit :+: (A :*: L)

  type ListF1[A] = Curry[      ListF    ]#λ[A]
  type ListF2[L] = Curry[ Flip[ListF]#λ ]#λ[L]

  type List[+A] = Fix[ListF1[A]#λ @uncheckedVariance]

  def listF1[A]: Functor[ListF1[A]#λ] = plus2[Unit, Prod2[A, I]#λ](prod2[A, I])
}

object TestFCategories extends FCategories {

  def main(args: Array[String]) {
  }
}
