import scala.language.higherKinds

trait FirstOrderKips {
  sealed trait Kips[F[X] <: Kips[F, X], S] {
    def map[T](f: S => T): F[T]
  }

  type KC[A] = { type λ[S] = K[A, S] }
  case class K[A, S](get: A) extends Kips[KC[A]#λ, S] {
    def map[T](f: S => T): K[A, T] = K(get)
  }

  case class I[S](get: S) extends Kips[I, S] {
    def map[T](f: S => T): I[T] = I(f(get))
  }

  type *#[F[X] <: Kips[F, X], G[Y] <: Kips[G, Y]] = {
    type λ[S] = :*:[F, G, S]
  }
  case class :*:
    [F[X] <: Kips[F, X], G[Y] <: Kips[G, Y], S]
    (_1: F[S], _2: G[S])
      extends Kips[*#[F, G]#λ, S]
  {
    def map[T](f: S => T): :*:[F, G, T] = :*:(_1 map f, _2 map f)

    // here because pattern-matching doesn't work
    def both[T](f: (F[S], G[S]) => T): T = f(_1, _2)
  }

  type +#[F[X] <: Kips[F, X], G[Y] <: Kips[G, Y]] = {
    type λ[S] = :+:[F, G, S]
  }
  sealed trait :+:[F[X] <: Kips[F, X], G[Y] <: Kips[G, Y], S]
      extends Kips[+#[F, G]#λ, S]
  {
    // here because pattern-matching doesn't work
    def either[T](f: F[S] => T, g: G[S] => T): T
  }

  case class L[F[X] <: Kips[F, X], G[Y] <: Kips[G, Y], S](get: F[S])
      extends :+:[F, G, S]
  {
    def map[T](f: S => T): L[F, G, T] = L(get map f)
    def either[T](f: F[S] => T, g: G[S] => T): T = f(get)
  }

  case class R[F[X] <: Kips[F, X], G[Y] <: Kips[G, Y], S](get: G[S])
      extends :+:[F, G, S]
  {
    def map[T](f: S => T): R[F, G, T] = R(get map f)
    def either[T](f: F[S] => T, g: G[S] => T): T = g(get)
  }

  trait Unroll[F[S] <: Kips[F, S], S <: Unroll[F, S]] {
    def unroll: F[S]

    def fold[T](f: F[T] => T): T = f(unroll map (_ fold f))
  }
}

trait Lists extends FirstOrderKips {
  type ListF[A, S] = :+:[KC[Unit]#λ, *#[KC[A]#λ, I]#λ, S]
  type ListC[A] = { type λ[S] = ListF[A, S] }

  def nilF[A, S]: ListF[A, S] =
    L[KC[Unit]#λ, *#[KC[A]#λ, I]#λ, S](K(()))

  def consF[A, S](a: A, s: S): ListF[A, S] =
    R[KC[Unit]#λ, *#[KC[A]#λ, I]#λ, S](:*:[KC[A]#λ, I, S](K(a), I(s)))

  sealed trait List[A] extends Unroll[ListC[A]#λ, List[A]]

  case class Nil[A]() extends List[A] {
    def unroll: ListF[A, List[A]] = nilF
  }

  case class Cons[A](head: A, tail: List[A]) extends List[A] {
    def unroll: ListF[A, List[A]] = consF(head, tail)
  }

  object List {
    // can't pattern match on listF due to type checker inadequacy
    def roll[A](listF: ListF[A, List[A]]): List[A] =
      listF either (
        nil => Nil(),
        cons => Cons(cons._1.get, cons._2.get))

    def apply[A](args: A*): List[A] =
      args.foldRight[List[A]](Nil())(Cons.apply)
  }
}

object TestFirstOrderKips extends Lists {
  def main(args: Array[String]) {
    val l1234 = List(1, 2, 3, 4)

    val sum = l1234.fold[Int](_ either (_ => 0, _ both (_.get + _.get)))

    println(s"sum($l1234) = $sum")
  }
}
