import reflect.{ClassTag, classTag}

// scrap your boilerplate

trait Scrap {
  // Newtype: here to get around not being able to extend final classes.
  trait Newtype[+T] {
    def get: T
    override def toString = get.toString
  }
  import language.implicitConversions
  implicit def autoUnboxNewtype[T](x: Newtype[T]): T = x.get
  implicit def autoBoxNewtype[T](x: T): Newtype[T] = new Newtype[T] { def get = x }

  // If x : T, then Hole(x) : T. This way a hole can be around everything.

  trait Hole[+T] {
    def getContentOfHole: T
    override def toString = s"Hole($getContentOfHole)"
  }

  object Hole {
    def unapply[T](x: T): Option[T] =
      x match {
        // has to use # and disregard path dependence
        // cannot require T: ClassTag. It would complain that
        // Scrap$$anon$2 cannot be cast to Scrap.
        case hole: Scrap#Hole[T] => Some(hole.getContentOfHole)

        case _ => None
      }

    // PRECONDITION: T is a trait
    // otherwise we'd run into all sorts of horrid mess
    def apply[T <: AnyRef : ClassTag](x: T): T = {
      // want to write: new Hole(x) with T
      // has to write:
      import net.sf.cglib.proxy._
      import java.lang.reflect.{Method, Constructor}
      val enhancer = new Enhancer
      val classT = classTag[T].runtimeClass
      val classHole = classTag[Hole[T]].runtimeClass
      enhancer setInterfaces Array(classT, classHole)
      enhancer setCallback new InvocationHandler {
        def invoke(proxy: Object, method: Method, args: Array[Object]): Object =
          method.getDeclaringClass match {
            // problem: messes up equal & hashcode.
            // we'd always have Hole(x) == x.
            case c if c == classHole => x
            case _ => method.invoke(x, args: _*)
          }
      }
      // Here's why T's gotta be an interface.
      // If it weren't, it cannot be created.
      enhancer.create.asInstanceOf[T]
    }
  }
}

object TestScrap extends Scrap {

  case class X(i: Newtype[Int])

  def main(args: Array[String]) {
    X(Hole(5)) match {
      case z @ X(Hole(n)) => println(z)
    }
  }
}
