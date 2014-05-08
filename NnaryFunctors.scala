import language.higherKinds
import language.implicitConversions
import annotation.unchecked.uncheckedVariance

trait Bifunctors {
  trait Bifunctor[F[_, _]] {
    def bimap[A, B, C, D]: (A => B) => (C => D) => F[A, C] => F[B, D]
  }

  case class :*:[+A, +B](_1: A, _2: B)
  sealed trait :+:[+A, +B]
  case class L[A](get: A) extends (A :+: Nothing)
  case class R[B](get: B) extends (Nothing :+: B)

  implicit class makeProduct[B](y: B) {
    def :*:[A](x: A): A :*: B = new :*:(x, y)
  }

  implicit object :*: extends Bifunctor[:*:] {
    def bimap[A, B, C, D] = f => g => { case x :*: y => f(x) :*: g(y) }
  }

  implicit object :+: extends Bifunctor[:+:] {
    def bimap[A, B, C, D] = f => g => { case L(x) => L(f(x)) ; case R(y) => R(g(y)) }
  }
}

trait NnaryFunctors extends Bifunctors {
  trait Functor[F[_]] {
    def fmap[A, B](f: A => B): F[A] => F[B]

    // appeal to the universal property of the initial algebra & compute
    // the unique morphism β to make the following diagram commute:
    //
    //  F[FixF]  ----[id]--->   FixF
    //
    //     |                     |
    //     | fmap(β)           β |
    //     V                     V
    //
    //    F[B]   -----[f]---->   B
    //

    def init[FixF <: F[FixF], T](f: F[T] => T)(x: FixF): T = f(fmap[FixF, T](init(f))(x))
  }

  // identity functor
  type ID[T] = T
  implicit object ID extends Functor[ID] {
    def fmap[X, Y](f: X => Y) = f
  }

  sealed trait ListF[+A, +B, +C]
  case class Nil[+A, +B, +C](get: A) extends ListF[A, B, C]
  case class Cons[+A, +B, +C](head: B, tail: C) extends ListF[A, B, C]

  sealed trait List[+A] extends ListF[Unit, A, List[A]] {
    // can't create a trait for fixed points, because context bound Functor[F]
    // demands constructor argument and we can't have that.
    def fold[T](f: ListF[Unit, A, T] => T): T = listF3[Unit, A, ID].init(f)(this)

    def map[B](f: A => B): List[B] =
      listF3[Unit, A, ID].init[List[A], List[B]](
        // you should really explore bifunctors a bit.
        // maybe they're all that's needed to make functors aware of all argument positions.
        ys => listF2[Unit, ID, List[B]].fmap(f)(ys)
      )(this)
  }

  implicit def fixListF[A, L <% List[A]](xs: ListF[Unit, A, L]): List[A] = xs match {
    case Nil(()) => new Nil(()) with List[A]
    case Cons(head, tail) => new Cons(head, tail: List[A]) with List[A]
  }

  type ListF1[F[_], B, C] = { type λ[A] = ListF[F[A], B, C] }
  type ListF2[A, F[_], C] = { type λ[B] = ListF[A, F[B], C] }
  type ListF3[A, B, F[_]] = { type λ[C] = ListF[A, B, F[C]] }

  def listF1[F[_]: Functor, B, C]: Functor[ListF1[F, B, C]#λ] = new Functor[ListF1[F, B, C]#λ] {
    def fmap[X, Y](f: X => Y): ListF[F[X], B, C] => ListF[F[Y], B, C] = _ match {
      case Nil(get) => new Nil(implicitly[Functor[F]].fmap(f)(get))
      case Cons(head, tail) => new Cons(head, tail)
    }
  }

  def listF2[A, F[_]: Functor, C]: Functor[ListF2[A, F, C]#λ] = new Functor[ListF2[A, F, C]#λ] {
    def fmap[X, Y](f: X => Y): ListF[A, F[X], C] => ListF[A, F[Y], C] = _ match {
      case Nil(get) => Nil(get)
      case Cons(head, tail) => new Cons(implicitly[Functor[F]].fmap(f)(head), tail)
    }
  }

  def listF3[A, B, F[_]: Functor]: Functor[ListF3[A, B, F]#λ] = new Functor[ListF3[A, B, F]#λ] {
    def fmap[X, Y](f: X => Y): ListF[A, B, F[X]] => ListF[A, B, F[Y]] = _ match {
      case Nil(get) => new Nil(get)
      case Cons(head, tail) => new Cons(head, implicitly[Functor[F]].fmap(f)(tail))
    }
  }
}

object TestNnaryFunctors extends NnaryFunctors {
  val xs: List[Int] = Cons(1, Cons(2, Cons(3, Cons(4, Cons(5, Nil(()))))))

  def main(args: Array[String]) {
    // sadly, can't leave out any test annotation.
    val Pi_xs = xs.fold[Int] {
      case Nil(_) => 1
      case Cons(m, n) => m * n
    }

    println(s"Π $xs = $Pi_xs")
  }
}
