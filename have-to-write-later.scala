import scala.language.implicitConversions

trait LambdaTerms {
  type TermAlgebra[T] = PartialFunction[TermFunctor[T], T]

  /** extension point: adding new data types */
  def fmapTerms[T, R](f: T => R): TermFunctor[T] => TermFunctor[R] = {
    case ConF(stant)   => ConF(stant)
    case AppF(fn, arg) => AppF(f(fn), f(arg))
    case VarF(binder)  => VarF(binder)
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

    def subst(from: Binder, to: Term): Term = subst(Map(from -> to))

    def subst(env: Map[Binder, Term]): Term = para[Term] { (before, after) =>
      before match {
        case binder: Binder if env isDefinedAt binder =>
          binder subst (env - binder)
        case _ => after match {
          case y: Bound[_] if env.isDefinedAt(y.binder) => env(y.binder)
          case otherwise => otherwise.toTerm
        }
      }
    }

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

  // What... a name-binding language?!

  type Env[T] = PartialFunction[Binder, T]

  // Note the lack of type recursion here
  trait Bound[T] extends TermFunctor[T] {
    def binder: Binder
    override def toString: String = binder.name
  }

  trait BinderFactory[T <: Binder] {
    def newBinder(): T
    def bound(binder: Binder): Term with Bound[Term]

    def apply(body: Term => Term): T = {
      val binder = newBinder
      binder.body = body(bound(binder))
      binder
    }

    def apply(defaultName: String)(body: Term => Term): T = {
      val binder = newBinder
      binder.defaultName = defaultName
      binder.body = body(bound(binder))
      binder
    }

    def unapply(b: T): Option[(Binder, Term)] = Some((b.binder, b.body))

    def replaceBody(binder: Binder, body: Term): Binder =
      apply(binder.defaultName) { x => body.subst(binder, x) }
  }

  trait Binder extends Term {
    // inherited from case class.
    // although the fields "binder" and "body" should be mutated
    // nowhere but here, we can't make them private to LambdaTerm
    // because each new case class (for a binder) defined elsewhere
    // has to "okay" their mutability.
    var binder: Binder
    var body: Term

    // cleverly loop to self
    binder = this

    lazy val name: String = christianMe(body)

    def apply(arg: Term): Term = (toFun[Term] { case x => x.toTerm })(arg)

    def toFun[T](algebra: TermAlgebra[T]): T => T = x => body.fold[T] {
      case y: Bound[_] if y.binder == this => x
      case otherwise => algebra(otherwise)
    }

    private[LambdaTerms]
    var defaultName: String = "x"

    private def christianMe(body: Term): String = {
      // - Do you renounce Satan?
      if (body == null)
        // - I do renounce him.
        sys error s"${getClass.getSimpleName}($defaultName, $body)"
      // - And all his works?
      val usedNames: Set[String] =
        body.traverse.flatMap({
          // - I do renounce them.
          case binder: Binder => Some(binder.name)
          case _ => None
        })(collection.breakOut)
      var myName = defaultName
      var startingIndex = -1
      var i = startingIndex
      // - And all his pomps?
      while (usedNames contains myName) {
        i = i + 1
        // - I do renounce them.
        if (i == startingIndex)
          sys error "oops, I've renounced everything."
        myName = defaultName + i
        // - Will you be baptized?
      }
      // - I will.
      // - In nomine Patri, et Filii, et Spiritus Sancti,
      //   Michael Rizzi, go in peace.
      myName
    }

    override val hashCode: Int = Binder.nextHashCode

    override def equals(other: Any): Boolean = other match {
      case other: Binder => other eq this // s.t. other: AnyRef
      case _ => false
    }

    override def toString: String =
      s"${getClass.getSimpleName}($name, $body)"
  }

  object Binder {
    private[LambdaTerms]
    var thisHashCode: Int = -1

    def nextHashCode(): Int = {
      thisHashCode += 1
      thisHashCode
    }
  }

  case class AbsF[T](var binder: Binder, var body: T) extends TermFunctor[T] {
    def toTerm: Term = body match {
      case body: Term => Abs.replaceBody(binder, body)
    }
  }
  class Abs(body: Term) extends AbsF[Term](null, body) with Binder
  object Abs extends BinderFactory[Abs] {
    def newBinder(): Abs = new Abs(null)
    def bound(binder: Binder): Var = Var(binder)
  }

  case class VarF[T](binder: Binder) extends Bound[T]
  { def toTerm: Term = Var(binder) }
  class Var(binder: Binder) extends VarF[Term](binder) with Term
  object Var {
    def apply(binder: Binder): Var = new Var(binder)
    def unapply(v: Var): Option[Binder] = Some(v.binder)
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

  implicit def stringToGlobalConstant(s: String): Term = Con(s)
}
