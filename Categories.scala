import language.higherKinds
import language.implicitConversions
import annotation.unchecked.uncheckedVariance

trait Categories {
  trait Category {
    type Object
    type Morphism[A <: Object, B <: Object]
  }

  object BaseCat extends Category {
    type Object = Any
    type Morphism[A, B] = A => B
  }

  trait Functor[Domain <: Category, Range <: Category] {
    type λ[X <: Domain#Object] <: Range#Object
    def fmap[A <: Domain#Object, B <: Domain#Object](f: Domain#Morphism[A, B]): Range#Morphism[λ[A], λ[B]]
  }

  class IdFun[C <: Category] extends Functor[C, C] {
    type λ[X <: C#Object] = X
    def fmap[A <: C#Object, B <: C#Object](f: C#Morphism[A, B]): C#Morphism[A, B] = f
  }

  // natural transformations (underconstrained; use with care.)
  trait NatT[
    Domain <: Category,
    Range <: Category,
    F <: Functor[Domain, Range],
    G <: Functor[Domain, Range]
  ] {
    def eta[X <: Domain#Object]: Range#Morphism[F#λ[X], G#λ[X]]
  }

  // functor category
  class FunCat[Domain <: Category, Range <: Category] extends Category {
    // objects are functors
    type Object = Functor[Domain, Range]

    // morphisms are natural transformations
    type Morphism[F <: Object, G <: Object] = Nothing
  }
}

object TestCategories extends Categories {
  def main(args: Array[String]) {
  }
}
