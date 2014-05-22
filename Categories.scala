import language.higherKinds
import language.implicitConversions
import annotation.unchecked.uncheckedVariance

trait Categories {
  trait Category {
    type Object
    type Morphism[A <: Object, B <: Object]
  }

  class BaseC extends Category {
    type Object = Any
    type Morphism[A, B] = A => B
  }

  trait Functor[Domain <: Category, Range <: Category] {
    type λ[X <: Domain#Object] <: Range#Object
    def fmap[A <: Domain#Object, B <: Domain#Object](f: Domain#Morphism[A, B]): Range#Morphism[λ[A], λ[B]]
  }

  class IdF[C <: Category] extends Functor[C, C] {
    type λ[X <: C#Object] = X
    def fmap[A <: C#Object, B <: C#Object](f: C#Morphism[A, B]): C#Morphism[A, B] = f
  }

  // natural transformations (underconstrained; use with care.)
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
      // must cast a null pointer; cannot say
      //     new ProductC[BaseC, C]#Morphism[λ[A], λ[B]] { ... }
      val c = null.asInstanceOf[ProductC[BaseC, C]]
      new c.Morphism[λ[A], λ[B]] {
        // _1 has to be identity function to preserve identity morphisms
        def _1: Int => Int = identity[Int]
        def _2: C#Morphism[A, B] = f
      }
    }
  }
}

object TestCategories extends Categories {
  def main(args: Array[String]) {
  }
}
