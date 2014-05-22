import reflect.{ClassTag, classTag}
import language.higherKinds

// scrap your boilerplate

trait Scrap {
  trait Gather[W[_]] {
    def apply[A: ClassTag, B: ClassTag](operator: W[A => B], operand: A): W[B]
  }

  trait Lift[W[_]] {
    def apply[A: ClassTag](a: A): W[A]
  }

  trait Data[Self] {
    def gfoldl[W[_]](gather: Gather[W], lift: Lift[W]): W[Self]

    private[this] type ID[T] = T

    def gmapT(fs: MkT[_]*): Self = gfoldl[ID](
      new Gather[ID] {
        def apply[A: ClassTag, B: ClassTag](operator: A => B, operand: A): B =
          operator(MkT.call(fs, operand))
      }
      ,
      new Lift[ID] {
        def apply[A: ClassTag](a: A): A = a
      }
    )

    /* problematic
    def everywhere(fs: MkT[_]*): Self = MkT.call(fs, gmapT(MkT[Data[_]]({
      case x => x.everywhere(fs: _*).asInstanceOf[Data[_]]
    })))
     */
  }

  case class MkT[T: ClassTag](f: PartialFunction[T, T]){
    def apply[A: ClassTag](x: A): Option[A] =
      if (classTag[A] == classTag[T]) { // the only thing that works
        val y = x.asInstanceOf[T]
        if (f isDefinedAt y)
          Some(f(y).asInstanceOf[A])
        else
          None
      }
      else
        None
  }

  object MkT {
    def call[A: ClassTag](fs: Seq[MkT[_]], x: A): A = {
      var maybe: Option[A] = None
      val fi = fs.iterator
      while (maybe == None && fi.hasNext) maybe = fi.next()(x)
      maybe match {
        case None => x
        case Some(y) => y
      }
    }
  }

  implicit class listDerivingData[T: ClassTag](xs: List[T]) extends Data[List[T]] {
    def gfoldl[W[_]](k: Gather[W], z: Lift[W]): W[List[T]] = xs match {
      case Nil =>
        z(Nil)

      case x :: xs =>
        // k (k (z (:)) x) xs
        k(k(z((x: T) => (xs: List[T]) => x :: xs), x), xs)
    }
  }
}

object TestScrap extends Scrap {

  def main(args: Array[String]) {
    val xs = Range(1, 10).toList
    val ys = xs.gmapT(MkT[Int] {
      case 1 => 100
      case 3 => 30
    })
    println(s"(1..9).gmapT(f) = $ys")
  }
}
