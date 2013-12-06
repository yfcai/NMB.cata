import scala.language.implicitConversions

/** The domain of values, implemented according to the principle
  * that primitives are free names in a bigger context.
  *
  * The method `lookupVal` looks up free names in the bigger
  * context. In our case, the bigger context is infinitely
  * big: it binds the name of all integer literals.
  */
trait Values {
  // superclass of all values
  trait Val {
    // try to call this value as if it's a function
    def apply(arg: Val): Val
  }

  // values of base type
  trait BaseVal extends Val {
    def apply(arg: Val): Val =
      sys error "type error: value of base type in operator position"
  }

  // the unique value of type Unit
  case object TT extends BaseVal

  // integers
  case class Num(n: Int) extends BaseVal

  // functions
  case class Fun(f: Val => Val) extends Val {
    def apply(arg: Val): Val = f(arg)
  }

  // fixed point of functions
  case class Fix(f: Val) extends Val {
    def apply(v: Val): Val = f(this)(v)
  }

  def liftVal2(f: (Int, Int) => Int): Fun = Fun {
    case Num(m) => Fun { case Num(n) => Num(f(m, n)) }
  }

  def lookupVal(s: String) = s match {
    // Number literals
    case s if s matches """(-)?\d+""" => Num(s.toInt)

    // Number primitives
    case "+" => liftVal2 (_ + _)
    case "-" => liftVal2 (_ - _)
    case "*" => liftVal2 (_ * _)
    case "/" => liftVal2 (_ / _)

    // if0 : ℤ → ∀α. (Unit → α) → (Unit → α) → α
    case "if0" => Fun {
      case Num(0) => Fun { x => Fun { y => x(TT) }}
      case _      => Fun { x => Fun { y => y(TT) }}
    }

    // Fixed-point operator!
    case "fix" => Fun(Fix)
  }
}

trait Names {
  /** We always want to keep the Name trait abstract and
    * extensible so that we can generate names that will
    * never collide with other names by declaring a private
    * subclass of Name.
    */
  trait Name {
    def get: String = this match {
      case StringLiteral(s) => s
      case _ => sys error "Type error: expect string literal!"
    }
  }

  case class StringLiteral(s: String) extends Name {
    override def toString = s
  }
}

trait AlgebraicDataType {
  type Algebra  [T] = PartialFunction[Functor[T], T]

  /** extension point: adding new data types */
  def fmap[T, R](f: T => R): Functor[T] => Functor[R] = {
    case x => sys error s"No clue how to map over $x"
  }

  trait Functor[T] {
    def map[R](f: T => R) = fmap(f)(this)
  }

  case class ADT(unroll: Functor[ADT]) extends Functor[ADT] {
    // catamorphism
    def fold[T](f: Algebra[T]): T = f(unroll map (_ fold f))
  }
}

trait LambdaExpr extends AlgebraicDataType with Names {
  override
  def fmap[T, R](f: T => R): Functor[T] => Functor[R] = {
    case Var(x)       => Var.Impl(x)
    case Abs(x, body) => Abs.Impl(x, f(body))
    case App(fn, arg) => App.Impl(f(fn), f(arg))
    case otherwise    => super.fmap(f)(otherwise)
  }

  object Var {
    def apply(x: Name): ADT = ADT(Impl(x))
    def unapply[T](e: Functor[T]): Option[Name] = e match {
      case ADT(unroll) => unapplyUnrolled(unroll)
      case _           => unapplyUnrolled(e)
    }

    private[this]
    def unapplyUnrolled[T](e: Functor[T]): Option[Name] = e match {
      case i: Impl[T] => Impl.unapply(i)
      case _          => None
    }

    private[LambdaExpr]
    case class Impl[T](val x: Name) extends Functor[T]
  }

  object App {
    def apply(fn: ADT, arg: ADT): ADT = ADT(Impl(fn, arg))
    def unapply[T](e: Functor[T]): Option[(T, T)] = e match {
      case ADT(unroll) => unapplyUnrolled(unroll)
      case _           => unapplyUnrolled(e)
    }

    private[this]
    def unapplyUnrolled[T](e: Functor[T]): Option[(T, T)] = e match {
      case i: Impl[T] => Impl.unapply(i)
      case _          => None
    }

    private[LambdaExpr]
    case class Impl[T](val fn: T, val arg: T) extends Functor[T]
  }

  object Abs {
    def apply(x: Name, body: ADT): ADT = ADT(Impl(x, body))
    def unapply[T](e: Functor[T]): Option[(Name, T)] = e match {
      case ADT(unroll) => unapplyUnrolled(unroll)
      case _           => unapplyUnrolled(e)
    }

    private[this]
    def unapplyUnrolled[T](e: Functor[T]): Option[(Name, T)] = e match {
      case i: Impl[T] => Impl.unapply(i)
      case _          => None
    }

    private[LambdaExpr]
    case class Impl[T](val x: Name, val body: T) extends Functor[T]
  }

  implicit def stringToName(s: String): Name = StringLiteral(s)
  implicit def stringToADT(s: String): ADT = Var(s)
}

trait Calculus extends AlgebraicDataType with Names with Values {
  type Env = PartialFunction[Name, Val]

  trait Evaluation {
    def withEnv(t: ADT): Env => Val
    val globalEnv: Env = { case x => lookupVal(x.get) }
    def apply(t: ADT) = withEnv(t)(globalEnv)
  }

  object eval extends Evaluation {
    def withEnv(t: ADT): Env => Val = t fold evalAlgebra
  }

  /** extension point: evaluation operation */
  def evalAlgebra: Algebra[Env => Val] = {
    case x => sys error s"No clue how to evaluate $x"
  }

  def pretty(t: ADT): String = t fold prettyAlgebra

  /** extension point: pretty print */
  def prettyAlgebra: Algebra[String] = {
    case x => sys error s"No clue how to pretty-print $x"
  }
}

trait LambdaCalculus extends Calculus with LambdaExpr {
  override def evalAlgebra: Algebra[Env => Val] = {
    case Var(x)       => _(x)
    case App(fn, arg) => env => fn(env)(arg(env))
    case Abs(x, body) => env => Fun {
      v => body(({ case y if x == y => v }: Env) orElse env)
    }
    case otherwise    => super.evalAlgebra(otherwise)
  }

  override def prettyAlgebra: Algebra[String] = {
    case Var(x)       => x.toString
    case Abs(x, body) => s"(λ$x. $body)"
    case App(fn, arg) => s"($fn $arg)"
    case otherwise    => super.prettyAlgebra(otherwise)
  }

  /** evaluation by pattern matching and explicit recursion
    * (for illustration purposes only)
    */
  object evalExplicit extends Evaluation {
    def withEnv(t: ADT): Env => Val = t match {
      case Var(x) => _(x)
      case App(fn, arg) => env => withEnv(fn)(env)(withEnv(arg)(env))
      case Abs(x, body) => env => Fun {
        v => withEnv(body)(({ case y if x == y => v }: Env) orElse env)
      }
    }
  }
}


trait DebugExpr extends AlgebraicDataType {
  override
  def fmap[T, R](f: T => R): Functor[T] => Functor[R] = {
    case Debug(x)       => Debug.Impl(f(x))
    case otherwise    => super.fmap(f)(otherwise)
  }

  object Debug {
    private[DebugExpr]
    case class Impl[T](t: T) extends Functor[T]
    def apply(t: ADT): ADT = ADT(Impl(t))
    def unapply[T](e: Functor[T]): Option[T] = e match {
      case ADT(unroll) => unapplyUnrolled(unroll)
      case _           => unapplyUnrolled(e)
    }

    private[this]
    def unapplyUnrolled[T](e: Functor[T]): Option[T] = e match {
      case i: Impl[T] => Impl.unapply(i)
      case _          => None
    }
  }
}

trait DebugCalculus extends Calculus with DebugExpr {
  override def evalAlgebra: Algebra[Env => Val] = {
    case Debug(t) => env => { val v = t(env) ; println(s"debug $v") ; v }
    case x      => super.evalAlgebra(x)
  }

  override def prettyAlgebra: Algebra[String] = {
    case Debug(t) => s"debug($t)"
    case x      => super.prettyAlgebra(x)
  }
}


object TestCalculus extends LambdaCalculus with DebugCalculus
import TestCalculus._

def test(t: => ADT) {
  println(s"${pretty(t)} = ${eval(t)}")
  println()
}

test { App(App("+", Debug("2")), Debug("2")) }

test {
  App(
    App("fix", Abs("f", Abs("n",
      App(App(App("if0", Debug("n")),
        Abs("_", "0")),
        Abs("_", App(App("+", "n"), App("f", App(App("-", "n"), "1")))))))),
    "10")
}

test {
  App(
    App("fix", Abs("f", Abs("n",
      App(App(App("if0", Debug("n")),
        Abs("_", "1")),
        Abs("_", App(App("*", "n"), App("f", App(App("-", "n"), "1")))))))),
    "5")
}
