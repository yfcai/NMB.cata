import language.higherKinds
import language.implicitConversions
import annotation.unchecked.uncheckedVariance

trait Categories {
  trait Category {
    type Object
    type Morphism[A <: Object, B <: Object]

    def id[X <: Object]: Morphism[X, X]
  }

  class BaseC extends Category {
    type Object = Any
    type Morphism[A, B] = A => B

    def id[X]: X => X = identity
  }

  trait Functor[Domain <: Category, Range <: Category] {
    type λ[X <: Domain#Object] <: Range#Object
    def fmap[A <: Domain#Object, B <: Domain#Object](f: Domain#Morphism[A, B]): Range#Morphism[λ[A], λ[B]]
  }

  class IdF[C <: Category] extends Functor[C, C] {
    type λ[X <: C#Object] = X
    def fmap[A <: C#Object, B <: C#Object](f: C#Morphism[A, B]): C#Morphism[A, B] = f
  }

  // natural transformations
  trait NaturalT[
    Domain <: Category,
    Range <: Category,
    F <: Functor[Domain, Range],
    G <: Functor[Domain, Range]
  ] {
    def eta[X <: Domain#Object]: Range#Morphism[F#λ[X], G#λ[X]]
  }

  // functor category
  class FunctorC[Domain <: Category, Range <: Category] extends Category {
    // objects are functors
    type Object = Functor[Domain, Range]

    // morphisms are natural transformations
    type Morphism[F <: Object, G <: Object] = NaturalT[Domain, Range, F, G]

    def id[F <: Object]: Morphism[F, F] = ???
  }

  trait ProductType[A, B] {
    // work around lack of variance reasoning
    type _1 <: A
    type _2 <: B
    def _1: _1
    def _2: _2
  }

  // product category
  class ProductC[C1 <: Category, C2 <: Category] extends Category {
    type Object = ProductType[C1#Object, C2#Object]

    // can't put this in companion object coz it depends on type Object
    trait Morphism[A <: Object, B <: Object] {
      def _1: C1#Morphism[A#_1, B#_1]
      def _2: C2#Morphism[A#_2, B#_2]
    }

    def id[X <: Object]: Morphism[X, X] = ???
  }

  // warm-up exercise: functor from cat to product with base
  // pretty horrible to write.
  class WithIntF[C <: Category] extends Functor[C, ProductC[BaseC, C]] {
    type λ[X <: C#Object] = ProductType[Any, C#Object] {
      type _1 = Int
      type _2 = X
    }

    def fmap[A <: C#Object, B <: C#Object](f: C#Morphism[A, B]):
        ProductC[BaseC, C]#Morphism[λ[A], λ[B]] = {
      val c = new ProductC[BaseC, C]
      new c.Morphism[λ[A], λ[B]] {
        // _1 has to be identity function to preserve identity morphisms
        def _1: Int => Int = identity[Int]
        def _2: C#Morphism[A, B] = f
      }
    }
  }

  // functor for products
  abstract class ProductF[C1 <: Category, C2 <: Category]
      extends Functor[C1, FunctorC[C2, ProductC[C1, C2]]] {

    type λ[X <: C1#Object] = Functor[C2, ProductC[C1, C2]] {
      type λ[Y <: C2#Object] = ProductType[C1#Object, C2#Object] {
        type _1 = X
        type _2 = Y
      }
    }

    def fmap[A <: C1#Object, B <: C1#Object](f: C1#Morphism[A, B]):
        NaturalT[C2, ProductC[C1, C2], λ[A], λ[B]] =
      new NaturalT[C2, ProductC[C1, C2], λ[A], λ[B]] {
        def eta[X <: C2#Object]: ProductC[C1, C2]#Morphism[λ[A]#λ[X], λ[B]#λ[X]] = {
          val c = new ProductC[C1, C2]
          new c.Morphism[λ[A]#λ[X], λ[B]#λ[X]] {
            def _1: C1#Morphism[A, B] = f
            def _2: C2#Morphism[X, X] = ??? // identity morphism...
          }
        }
      }
  }
}

object TestCategories extends Categories {
  def main(args: Array[String]) {
  }
}
