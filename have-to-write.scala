import scala.language.implicitConversions

trait HaveToWrite {
  type TermAlgebra[T] = PartialFunction[TermFunctor[T], T]

  /** extension point: adding new data types */
  def fmapTerms[T, R](f: T => R): TermFunctor[T] => TermFunctor[R] = {
    case ConF(stant)   => ConF(stant)
    case AppF(fn, arg) => AppF(f(fn), f(arg))
    case VarF(name)    => VarF(name)
    case AbsF(x, body) => AbsF(x, f(body))
    case x => sys error s"No clue how to map over $x"
  }

  trait TermFunctor[T] {
    def map[R](f: T => R) = fmapTerms(f)(this)
    def toTerm: Term
  }

  case class ParaTerm(functor: TermFunctor[(Term, ParaTerm)]) {
    def fold[T](f: (=> Term, => TermFunctor[T]) => T): T =
      f(functor.map(_._1).toTerm, functor map { _._2 fold f})
  }

  // We cheat out of the boilerplates of yet another functor
  // by mutation.
  object ParaTerm {
    def apply(adt: Term): ParaTerm = {
      var traversed = adt.traverse
      adt.fold[(Term, ParaTerm)]({
        case functor =>
          val result = (traversed.head, ParaTerm(functor))
          traversed = traversed.tail
          result
      })._2
    }
  }

  trait Term extends TermFunctor[Term] {
    // catamorphism
    def fold[T](f: TermAlgebra[T]): T = f(this map (_ fold f))

    // paramorphism.
    // if a normal function (not a case function) is given as argument,
    // then para does not recurse unless necessary.
    // this is important if the Term has a cycle.
    def para[T](f: (=> Term, => TermFunctor[T]) => T): T = ParaTerm(this) fold f
    /** gives a list of Terms in traversal order */
    def traverse: List[Term] = {
      var traversed: List[Term] = Nil
      fold[Term] {
        case s: TermFunctor[Term] =>
          val visiting = s.toTerm
          traversed = visiting :: traversed
          visiting
      }
      traversed.reverse
    }
  }

  case class AbsF[T](name: String, body: T) extends TermFunctor[T] {
    def toTerm: Term = body match {
      case body: Term => Abs(name, body)
    }
  }
  class Abs(name: String, body: Term) extends AbsF[Term](name, body) with Term {
    override def toString: String =
      s"${getClass.getSimpleName}($name, $body)"
  }
  object Abs {
    def apply(name: String, body: Term): Abs = Abs(name, body)
    def unapply(v: Abs): Option[(String, Term)] = Some((v.name, v.body))
  }

  case class VarF[T](name: String) extends TermFunctor[T]
  { def toTerm: Term = Var(name) }
  class Var(name: String) extends VarF[Term](name) with Term {
    override def toString: String =
      s"${getClass.getSimpleName}($name)"
  }
  object Var {
    def apply(name: String): Var = new Var(name)
    def unapply(v: Var): Option[String] = Some(v.name)
  }

  case class AppF[T](fun: T, arg: T) extends TermFunctor[T] {
    def toTerm: Term = (fun, arg) match {
      case (fun: Term, arg: Term) => App(fun, arg)
    }
  }
  class App(fun: Term, arg: Term) extends AppF[Term](fun, arg) with Term {
    override def toString: String =
      s"${getClass.getSimpleName}($fun, $arg)"
  }
  object App {
    def apply(fun: Term, arg: Term): App = new App(fun, arg)
    def unapply(a: App): Option[(Term, Term)] = Some((a.fun, a.arg))
  }

  case class ConF[T](stant: String) extends TermFunctor[T]
  { def toTerm: Term = Con(stant) }
  class Con(stant: String) extends ConF[Term](stant) with Term {
    override def toString: String =
      s"${getClass.getSimpleName}($stant)"
  }
  object Con {
    def apply(stant: String): Con = new Con(stant)
    def unapply(c: Con): Option[String] = Some(c.stant)
  }
}
