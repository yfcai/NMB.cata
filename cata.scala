import scala.language.implicitConversions

trait Values {
  // value domain! runtime type system!
  type =>:[Domain, Range] = PartialFunction[Domain, Range]
  sealed trait Val {
    def apply(arg: Val): Val
  }

  trait BaseVal extends Val {
    def apply(arg: Val): Val = sys error "runtime type error lol"
  }

  case object TT extends BaseVal
  case class Num(n: Int) extends BaseVal

  case class Fun(f: Val =>: Val) extends Val {
    def apply(arg: Val): Val = f(arg)
  }

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

    // Church Boolean!
    case "if0" => Fun {
      case Num(0) => Fun { case x => Fun { case y => x(TT) }}
      case _      => Fun { case x => Fun { case y => y(TT) }}
    }

    // Fixed-point operator!
    case "fix" => Fun { case f => Fix(f) }
  }
}

object Namely extends Values {
  trait Name {
    def get: String = this match {
      case StringLiteral(s) => s
      case _ => sys error "Type error: expect string literal!"
    }
  }

  case class StringLiteral(s: String) extends Name {
    override def toString = s
  }

  implicit def stringToName(s: String): Name = StringLiteral(s)
  implicit def stringToExp(s: String): Exp = Var(s)

  // ExpF is the functor whose fixed point is Exp
  sealed trait ExpF[T]
  case class VarF[T](x: Name) extends ExpF[T]
  case class AbsF[T](x: Name, body: T) extends ExpF[T]
  case class AppF[T](fn: T, arg: T) extends ExpF[T]

  // illegal cyclic reference involving type Exp
  // type Exp = ExpF[Exp]

  // ... will write the fixed point by hand.

  case class Var(x: Name) extends Exp
  case class Abs(x: Name, body: Exp) extends Exp
  case class App(fn: Exp, arg: Exp) extends Exp

  sealed trait Exp {
    def fold[T](f: ExpF[T] => T): T = this match {
      case Var(x) => f(VarF[T](x))
      case Abs(x, body) => f(AbsF[T](x, body fold f))
      case App(fn, arg) => f(AppF[T](fn fold f, arg fold f))
    }
  }

  object eval {
    type Env = Name =>: Val

    val globalEnv: Env = { case x => lookupVal(x.get) }

    def withEnv(t: Exp) = t.fold[Env => Val] {
      case VarF(x) => _(x)

      case AbsF(x, body) => env => Fun {
        case v => body {
          case name if x == name => v
          case otherwise         => env(otherwise)
        }
      }

      case AppF(fn, arg) => env => fn(env)(arg(env))
    }

    def apply(t: Exp) = eval.withEnv(t)(globalEnv)
  }

  object pretty {
    def apply(t: Exp) = t.fold[String] {
      case VarF(x) => x.toString

      case AbsF(x, body) => s"(λ$x. $body)"

      case AppF(fn, arg) => s"($fn $arg)"
    }
  }

  def test(t: => Exp) {
    println(s"${pretty(t)} = ${eval(t)}")
    println()
  }

  test {
    App(App("+", "2"), "2")
  }

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

object Nameless extends Values {
  sealed trait ExpF[T]
  case class AbsF[T](body: T => T) extends ExpF[T]
  case class AppF[T](fn: T, arg: T) extends ExpF[T]

  object Exp {
    def fmap[A, B](f: A => B, g: B => A): ExpF[A] => ExpF[B] = {
      case AbsF(body)    => AbsF(f compose body compose g)
      case AppF(fn, arg) => AppF(f(fn), f(arg))
    }
  }

  case class PlaceHolder[T](get: T) extends Exp[T] {
    def unroll: ExpF[Exp[T]] = sys error "unrolling placeholder?!"
  }

  case class App[T](fn: Exp[T], arg: Exp[T]) extends Exp[T] {
    def unroll: ExpF[Exp[T]] = AppF(fn, arg)
  }

  case class Abs[T](body: Exp[T] => Exp[T]) extends Exp[T] {
    def unroll: ExpF[Exp[T]] = AbsF(body)
  }

  sealed trait Exp[T] {
    def unroll: ExpF[Exp[T]]

    def fold(f: ExpF[T] => T): T = this match {
      case PlaceHolder(value) => value
      case _ => f(Exp.fmap[Exp[T], T](_.fold(f), PlaceHolder.apply)(unroll))
    }
  }

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
        case AbsF(body)    => { val x = name.next ; s"(λ$x. ${body(x)})" }
        case AppF(fn, arg) => s"($fn $arg)"
      }
    }
  }

  object eval {
    def apply(t: Exp[Val]): Val = t.fold {
      case AbsF(body)    => Fun { case x => body(x) }
      case AppF(fn, arg) => fn(arg)
    }
  }

  implicit def anyToExp[T](s: T): Exp[T] = PlaceHolder(s)
  implicit def integerLiteral(n: Int): Exp[Val] = Num(n)
  implicit def prettyIntLit(n: Int): Exp[String] = n.toString
  implicit def stringToExpVal(s: String): Exp[Val] = lookupVal(s)

  // this function is impossible because Scala lacks
  // first class polymorphism
  //
  // def test(t[T]: => Exp[T]) {
  //   println(s"${pretty(t)} = ${eval(t)}")
  //   println()
  // }

  def test(t1: => Exp[String])(t2: => Exp[Val]) {
    println(s"${pretty(t1)} = ${eval(t2)}")
    println()
  }

  test { App(App("+", 2), 2) } { App(App("+", 2), 2) }

  test {
    App(
      App("fix", Abs(f => Abs(n =>
        App(App(App("if0", n),
          Abs(_ => 0)),
          Abs(_ => App(App("+", n), App(f, App(App("-", n), 1)))))))),
      10)
  } {
    App(
      App("fix", Abs(f => Abs(n =>
        App(App(App("if0", n),
          Abs(_ => 0)),
          Abs(_ => App(App("+", n), App(f, App(App("-", n), 1)))))))),
      10)
  }

  test {
    App(
      App("fix", Abs(f => Abs(n =>
        App(App(App("if0", n),
          Abs(_ => 1)),
          Abs(_ => App(App("*", n), App(f, App(App("-", n), 1)))))))),
      5)
  } {
    App(
      App("fix", Abs(f => Abs(n =>
        App(App(App("if0", n),
          Abs(_ => 1)),
          Abs(_ => App(App("*", n), App(f, App(App("-", n), 1)))))))),
      5)
  }

}
