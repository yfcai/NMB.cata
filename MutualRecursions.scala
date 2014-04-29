// mutually recursive types supported by the functor type class

import language.higherKinds

trait MutualRecursions {
  trait Functor[F[_]] {
    def fmap[A, B](f: A => B)(fa: F[A]): F[B]
  }

  // 1. TREE: mutually recursive with a higher-order type

  // sadly, Functor is invariant in F.
  // every library function needs an instance declaration.
  implicit def listFunctor: Functor[List] = new Functor[List] {
    def fmap[A, B](f: A => B)(fa: List[A]): List[B] = fa map f
  }

  sealed trait Tree {
    def unroll: TreeF[Tree]
    def fold[T](f: TreeF[T] => T): T = f(unroll map (_ fold f))
  }
  case class Leaf(tag: Int) extends Tree { def unroll = LeafF(tag) }
  case class Branch(children: List[Tree]) extends Tree { def unroll = BranchF(children) }

  object Tree {
    def roll(treeF: TreeF[Tree]): Tree = treeF match {
      case LeafF(tag) => Leaf(tag)
      case BranchF(children) => Branch(children)
    }
  }

  sealed trait TreeF[R] {
    def map[S](f: R => S)
      (implicit sf: Functor[List]): // here: all functor instance declarations
        TreeF[S]
  }

  object TreeF {
    implicit def treeFunctor: Functor[TreeF] = new Functor[TreeF] {
      def fmap[A, B](f: A => B)(fa: TreeF[A]): TreeF[B] = fa map f
    }
  }

  case class LeafF[R](tag: Int) extends TreeF[R] {
    def map[S](f: R => S)(implicit sf: Functor[List]): TreeF[S] = LeafF(tag)
  }

  case class BranchF[R](children: List[R]) extends TreeF[R] {
    def map[S](f: R => S)(implicit sf: Functor[List]): TreeF[S] = BranchF(sf.fmap(f)(children))
  }

  // 2. EVEN/ODD: mutually recursive with each other
  //    pretty complicated, but every type falling under this case
  //    is totally within the macro's control

  // universal type  ∀idx. EvenOddF s idx → s idx
  trait EvenOddAlgebra[S[_]] {
    def apply[Idx]: EvenOddF[S, Idx] => S[Idx]
  }

  sealed trait EvenOdd[Idx] {
    this: Idx => // scala can't use this to figure out that EvenOdd[Odd] <: Odd, sadly
    def unroll: EvenOddF[EvenOdd, Idx]

    def fold[S[_]](f: EvenOddAlgebra[S]): S[Idx] =
      f apply (unroll map new EvenOddArrow[EvenOdd, S] {
        def apply[J] = _ fold f
      })
  }

  object EvenOdd {
    def roll[Idx](body: EvenOddF[EvenOdd, Idx]): Idx = body match {
      case ZeroF => Zero
      case EsucF(pred) => Esuc(roll(pred.unroll)) // Esuc(pred) doesn't work;
      case OsucF(pred) => Osuc(roll(pred.unroll)) // see the `this: Idx =>` comment
    }
  }

  sealed trait Even extends EvenOdd[Even]

  case object Zero extends Even {
    def unroll = ZeroF
  }
  case class Esuc(pred: Odd) extends Even {
    def unroll = EsucF(pred)
  }

  sealed trait Odd extends EvenOdd[Odd]
  case class Osuc(pred: Even) extends Odd {
    def unroll = OsucF(pred)
  }

  type AllForNothing[_] = Nothing

  // universal type  ∀idx. r idx → s idx
  trait EvenOddArrow[-R[_], +S[_]] {
    def apply[Idx]: R[Idx] => S[Idx]
  }

  sealed trait EvenOddF[+R[_], Idx] {
    def map[S[_]](f: EvenOddArrow[R, S]): EvenOddF[S, Idx]
  }

  case object ZeroF extends EvenOddF[AllForNothing, Even] {
    def map[S[_]](f: EvenOddArrow[AllForNothing, S]): EvenOddF[S, Even] = ZeroF
  }

  case class EsucF[+R[_]](pred: R[Odd]) extends EvenOddF[R, Even] {
    def map[S[_]](f: EvenOddArrow[R, S]): EvenOddF[S, Even] = EsucF(f apply pred)
  }

  case class OsucF[+R[_]](pred: R[Even]) extends EvenOddF[R, Odd] {
    def map[S[_]](f: EvenOddArrow[R, S]): EvenOddF[S, Odd] = OsucF(f apply pred)
  }
}

object TestMutualRecursions extends MutualRecursions { def main(args: Array[String]) {
  val tree: Tree =
    Branch(List(
      Branch(List(
        Leaf(1),
        Leaf(2))),
      Leaf(3),
      Branch(List(
        Leaf(4),
        Leaf(5)))))

  def sumLeaves(t: Tree): Int = t.fold[Int] {
    case LeafF(n) => n
    case BranchF(ns) => ns.sum
  }

  val evenNumberSix: Even = Esuc(Osuc(Esuc(Osuc(Esuc(Osuc(Zero))))))

  type AllForInt[_] = Int

  def toInt(e: Even): Int = e fold new EvenOddAlgebra[AllForInt] {
    def apply[Idx] = _ match {
      case ZeroF => 0
      case EsucF(pred) => pred + 1
      case OsucF(pred) => pred + 1
    }
  }

  println(s"sumLeaves( [[1, 2], 3, [4, 5]] ) = ${sumLeaves(tree)}")
  println(s"toInt(evenNumberSix) = ${toInt(evenNumberSix)}")
}}
