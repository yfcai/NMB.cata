/** Formalizing category theory in scala does not seem practical.
  * Nevertheless, you gained insight about natural transformations:
  *
  * A natural transformation is mapping against one argument of
  * a curried multivariate functor.
  */

import language.higherKinds

trait Categories {
  categories =>

  trait Type {
    type Type
    def :*: (lhs: categories.Type) = new :*:(lhs, this)
    def :+: (lhs: categories.Type) = new :+:(lhs, this)
  }

  trait Category {
    type Object <: AnyRef
    type Morphism <: ProtoMorphism
    def id(x: Object): Morphism

    trait ProtoMorphism {
      val domain: Object
      val range: Object
    }
  }

  // constant categories are objects
  object ScalaC extends Category {
    type Object = Type
    trait Morphism extends ProtoMorphism {
      def apply(x: domain.Type): range.Type
    }
    def id(x: Object) = new Morphism {
      val domain: x.type = x
      val range: x.type = x
      def apply(y: x.Type): x.Type = y
    }
  }

  trait Functor {
    val domain: Category
    val range: Category
    def map(x: domain.Object): range.Object
    def fmap(f: domain.Morphism): range.Morphism
  }

  trait Endofunctor extends Functor {
    val category: Category
    val domain: category.type = category
    val range : category.type = category
  }

  // concrete functors are case classes
  case class IdF(c: Category) extends Functor {
    import c.{Object, Morphism}
    val domain: c.type = c
    val range: c.type = c
    def map(x: Object): Object = x
    def fmap(f: Morphism): Morphism = f
  }

  // concrete categories are traits
  trait FunctorC extends Category {
    functorC =>
    val c1: Category
    val c2: Category
    type Object = Functor
    type Morphism = NaturalTransformation

    def id(f: Object): Morphism = new NaturalTransformation {
      val domain = f
      val range  = f
      def eta(x: c1.Object): c2.Morphism = c2.id(f map x)
    }

    trait Functor extends categories.Functor {
      val domain: c1.type
      val range : c2.type
    }

    trait NaturalTransformation extends ProtoMorphism {
      def eta(x: c1.Object): c2.Morphism
    }
  }

  trait ProductC extends Category {
    val c1: Category
    val c2: Category

    type Object = (c1.Object, c2.Object)

    case class Morphism(
      domain: Object, range: Object,
      _1: c1.Morphism, _2: c2.Morphism
    ) extends ProtoMorphism

    def id(x: Object): Morphism = Morphism(x, x, c1.id(x._1), c2.id(x._2))
  }

  // functor from c1 to the functor category from c2 to the product category c1 × c2
  case class ProductF(c1: Category, c2: Category) extends Functor {
    productF =>

    val product = new ProductC {
      val c1: ProductF.this.c1.type = ProductF.this.c1
      val c2: ProductF.this.c2.type = ProductF.this.c2
    }

    val domain: c1.type = c1
    val range = new FunctorC {
      val c1: ProductF.this.c2.type = ProductF.this.c2
      val c2: ProductF.this.product.type = ProductF.this.product
    }

    def map(x: c1.Object): C2ToProduct = new C2ToProduct {
      def map(y: c2.Object): product.Object = (x, y)
      def fmap(g: c2.Morphism): product.Morphism =
        product.Morphism((x, g.domain), (x, g.range), c1 id x, g)
    }

    def fmap(f: c1.Morphism): range.Morphism = new range.NaturalTransformation {
      val domain: C2ToProduct = productF map f.domain
      val range : C2ToProduct = productF map f.range
      def eta(x: c2.Object): product.Morphism =
        product.Morphism((f.domain, x), (f.range, x), f, c2 id x)
    }

    trait C2ToProduct extends range.Functor {
      val domain: c2.type = c2
      val range: product.type = product
    }
  }

  def fix(f: Endofunctor): f.category.Object = f map fix(f)

  object Unit extends Type {
    type Type = Unit
  }

  case class :*:(_1: Type, _2: Type) extends Type {
    type Type = (_1.Type, _2.Type)
  }

  case class :+:(left: Type, right: Type) extends Type {
    type Type = Either[left.Type, right.Type]
  }

  trait ListPatternFunctor extends Functor {
    listF =>
    import ScalaC.Morphism

    val domain = ScalaC
    val range = new FunctorC {
      val c1: ScalaC.type = ScalaC
      val c2: ScalaC.type = ScalaC
    }

    def map(x: Type): ScalaEndofunctor = new ListFunctor2(x)

    def fmap(f: Morphism): range.Morphism = new range.NaturalTransformation {
      val domain = listF map f.domain

      val range  = listF map f.range

      def eta(x: Type): Morphism = new Morphism {
        val domain = Unit :+: (f.domain :*: x)
        val range  = Unit :+: (f.range  :*: x)
        def apply(xs: domain.Type): range.Type = xs match {
          case Left(_) => Left(().asInstanceOf[range.left.Type])
          case Right((y, ys)) => Right((
            f(y.asInstanceOf[f.domain.Type]),
            ys)).asInstanceOf[range.Type]
          case _ => sys error "OMG LOOK AT ALL THOSE CASTS"
        }
      }
    }

    trait ScalaEndofunctor extends range.Functor with Endofunctor {
      import ScalaC.{Object, Morphism}
      val category = ScalaC
    }

    class ListFunctor2(x: Type) extends ScalaEndofunctor {
      def map(y: Type): Type = Unit :+: (x :*: y) // or even nominal
      def fmap(f: Morphism): Morphism = new Morphism {
        // exasperated sigh
        val xfd = x :*: f.domain
        val xfr = x :*: f.range
        val domain = new :+: (Unit, xfd) {
          override val left: Unit.type = Unit
          override val right: xfd.type = xfd
        }
        val range  = new :+: (Unit, xfr) {
          override val left: Unit.type = Unit
          override val right: xfr.type = xfr
        }
        def apply(xs: domain.Type): range.Type = xs match {
          case Left(()) => Left(())
          case Right((head, tail)) => Right((
            head.asInstanceOf[range.right._1.Type],
            f(tail.asInstanceOf[f.domain.Type]).
              asInstanceOf[range.right._2.Type]
          ))
        }
      }
    }
  }
}
