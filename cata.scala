import scala.language.implicitConversions

/** The domain of values, implemented according to the principle
  * that primitives are free names in a bigger context.
  *
  * The method `lookupVal` looks up free names in the bigger
  * context. In our case, the bigger context is infinitely
  * big: it binds the name of all integer literals.
  */
trait Values {
  type =>:[Domain, Range] = PartialFunction[Domain, Range]

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

trait NamelyAlgebra extends Names {
  // ExpFunctor is the functor whose fixed point is Exp
  sealed trait ExpFunctor[T]

  import UnionType.Or

  object Var {
    def apply(x: Name): Exp = Impl[Exp](x)
    def unapply[T](e: Impl[T]): Option[Name] = Impl.unapply(e)

    private[NamelyAlgebra]
    case class Impl[T](val x: Name) extends ExpFunctor[T]
  }

  object App {
    def apply(fn: Exp, arg: Exp): Exp = Impl[Exp](fn, arg)
    def unapply[T](e: Impl[T]): Option[(T, T)] = Impl.unapply(e)

    private[NamelyAlgebra]
    case class Impl[T](val fn: T, val arg: T) extends ExpFunctor[T]
  }

  object Abs {
    def apply(x: Name, body: Exp): Exp = Impl[Exp](x, body)
    def unapply[T](e: Impl[T]): Option[(Name, T)] = Impl.unapply(e)

    private[NamelyAlgebra]
    case class Impl[T](val x: Name, val body: T) extends ExpFunctor[T]
  }

  // Scala doesn't support type-level recursions like
  //
  //     type Exp = ExpFunctor[Exp]
  //
  // So we have to roll the fixed point of a functor by hand.

  implicit class Exp(private[NamelyAlgebra] val unroll: ExpFunctor[Exp]) {
    def fold[T](f: ExpFunctor[T] => T): T = unroll match {
      case Var(x)       => f(Var.Impl(x))
      case Abs(x, body) => f(Abs.Impl(x, body fold f))
      case App(fn, arg) => f(App.Impl(fn fold f, arg fold f))
    }
  }
}

/** Catamorphism for syntax trees with names */
object Namely extends NamelyAlgebra with Values {
  implicit def stringToName(s: String): Name = StringLiteral(s)
  implicit def stringToExp(s: String): Exp = Var(s)

  object eval {
    type Env = PartialFunction[Name, Val]

    val globalEnv: Env = { case x => lookupVal(x.get) }

    def withEnv(t: Exp) = t.fold[Env => Val] {
      case Var(x) => _(x)

      case Abs(x, body) => env => Fun {
        v => body(({ case y if x == y => v }: Env) orElse env)
      }

      case App(fn, arg) => env => fn(env)(arg(env))
    }

    def apply(t: Exp) = eval.withEnv(t)(globalEnv)
  }

  object pretty {
    def apply(t: Exp) = t.fold[String] {
      case Var(x)       => x.toString
      case Abs(x, body) => s"(λ$x. $body)"
      case App(fn, arg) => s"($fn $arg)"
    }
  }

  def test(t: => Exp) {
    println(s"${pretty(t)} = ${eval(t)}")
    println()
  }

  test { App(App("+", "2"), "2") }

  test {
    App(
      App("fix", Abs("f", Abs("n",
        App(App(App("if0", "n"),
          Abs("_", "0")),
          Abs("_", App(App("+", "n"), App("f", App(App("-", "n"), "1")))))))),
      "10")
  }

  test {
    App(
      App("fix", Abs("f", Abs("n",
        App(App(App("if0", "n"),
          Abs("_", "1")),
          Abs("_", App(App("*", "n"), App("f", App(App("-", "n"), "1")))))))),
      "5")
  }
}

trait NamelessAlgebra {
  sealed trait ExpFunctor[T]
  object Abs {
    def apply[T](body: Exp[T] => Exp[T]): Exp[T] = Impl[Exp[T]](body)
    def unapply[T](e: Impl[T]): Option[T => T] = Impl.unapply(e)

    private[NamelessAlgebra]
    case class Impl[T](val body: T => T) extends ExpFunctor[T]
  }

  object App {
    def apply[T](fn: Exp[T], arg: Exp[T]): Exp[T] = Impl[Exp[T]](fn, arg)
    def unapply[T](e: Impl[T]): Option[(T, T)] = Impl.unapply(e)

    private[NamelessAlgebra]
    case class Impl[T](val fn: T, val arg: T) extends ExpFunctor[T]
  }

  // This time Exp isn't the fixed point of ExpFunctor. Rather,
  // An inhabitant of Exp[T] is an expression tree with T at the
  // leaves; it can fold to a value of type T and nothing else.
  // The real fixed point of ExpFunctor is isomorphic to
  // (∀T. Exp[T]). Scala hasn't first-class polymorphism.
  // We make do by implicit conversion.

  case class ExpRoll[T](unroll: ExpFunctor[Exp[T]]) extends Exp[T]
  case class Placeholder[T](v: T) extends Exp[T] {
    def unroll: ExpFunctor[Exp[T]] = sys error "unrolling placeholder?"
  }

  implicit def functorToExp[T](f: ExpFunctor[Exp[T]]): Exp[T] = ExpRoll(f)

  object Exp {
    def fmap[A, B](f: A => B, g: B => A): ExpFunctor[A] => ExpFunctor[B] = {
      case Abs(body)    => Abs.Impl(f compose body compose g)
      case App(fn, arg) => App.Impl(f(fn), f(arg))
    }
  }

  sealed trait Exp[T] {
    def unroll: ExpFunctor[Exp[T]]
    def fold(f: ExpFunctor[T] => T): T = this match {
      case Placeholder(value) => value
      case _ => f(Exp.fmap[Exp[T], T](_.fold(f), Placeholder.apply)(unroll))
    }
  }
}

/** Catamorphism for nameless higher-order abstract syntax */
object Nameless extends NamelessAlgebra with Values {
  object pretty {
    private class NameGenerator {
      var index = 0
      def next: String = {
        index = index + 1
        "x" + index
      }
    }

    def apply(t: Exp[String]) = {
      val name = new NameGenerator
      t.fold {
        case Abs(body)    => { val x = name.next ; s"(λ$x. ${body(x)})" }
        case App(fn, arg) => s"($fn $arg)"
      }
    }
  }

  object eval {
    def apply(t: Exp[Val]): Val = t.fold {
      case Abs(body)    => Fun { case x => body(x) }
      case App(fn, arg) => fn(arg)
    }
  }

  implicit def anyToExp[T](s: T): Exp[T] = Placeholder(s)
  implicit def stringToExpVal(s: String): Exp[Val] = lookupVal(s)

  // Faking (∀T. Exp[T])

  def ex1[T](implicit _cs: String => Exp[T]): Exp[T] =
    App(App("+", "2"), "2")

  def ex2[T](implicit _cs: String => Exp[T]): Exp[T] =
    App(
      App("fix", Abs(f => Abs(n =>
        App(App(App("if0", n),
          Abs(_ => "0")),
          Abs(_ => App(App("+", n), App(f, App(App("-", n), "1")))))))),
      "10")

  def ex3[T](implicit _cs: String => Exp[T]): Exp[T] =
    App(
      App("fix", Abs(f => Abs(n =>
        App(App(App("if0", n),
          Abs(_ => "1")),
          Abs(_ => App(App("*", n), App(f, App(App("-", n), "1")))))))),
      "5")

  def test(t1: Exp[String])(t2: Exp[Val]) {
    println(s"${pretty(t1)} = ${eval(t2)}")
    println()
  }

  test(ex1)(ex1)
  test(ex2)(ex2)
  test(ex3)(ex3)
}
