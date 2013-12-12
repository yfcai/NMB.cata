import scala.language.implicitConversions
import scala.util.hashing.MurmurHash3

trait NameBindingLanguage {
  type Algebra  [T] = PartialFunction[Functor[T], T]
  type Coalgebra[T] = PartialFunction[T, Functor[T]]

  /** extension point: adding new data types */
  def fmap[T, R](f: T => R): Functor[T] => Functor[R] = {
    case x => sys error s"No clue how to map over $x"
  }

  trait Functor[T] {
    def map[R](f: T => R) = fmap(f)(this)
  }

  object ADT {
    // anamorphism
    def ana[T](psi: Coalgebra[T])(x: T): ADT = ADT(psi(x) map (ana(psi)))
  }

  case class ADT(unroll: Functor[ADT]) extends Functor[ADT] {
    // catamorphism
    def fold[T](f: Algebra[T]): T = f(unroll map (_ fold f))

    // paramorphism
    def para[T](f: (ADT, Functor[T]) => T): T = {
      var traversed = traverse
      fold[T] {
        case s: Functor[T] =>
          val result = f(traversed.head, s)
          traversed = traversed.tail
          result
      }
    }

    def traverse: List[ADT] = {
      // We cheat out of the boilerplates of yet another functor
      // by mutation. Mutation is the back door to escape to
      // Turing completeness---and in Hardin's words, the last
      // refuge of the incompetent (or impatient). If the
      // language support of something isn't perfect (and it is
      // rarely the case for everything), wouldn't it make more
      // sense to leave the option open for a less robust
      // solution, instead of forbidding it altogether?
      var traversed: List[ADT] = Nil
      fold[ADT] {
        case s: Functor[ADT] =>
          val visiting = ADT(s)
          traversed = visiting :: traversed
          visiting
      }
      traversed.reverse
    }
  }

  // What... a name-binding language?!

  // Note the lack of type recursion here
  trait Bound[T] extends Functor[T] {
    def binder: Binder[ADT]
    override def toString: String = binder.name
  }

  trait Binder[T] extends Functor[T] {
    def defaultName: String
    var body: T

    def toHOAS: ADT => ADT = algebraicFun[ADT] { case x => ADT(x) }

    // Maybe a trampoline's what's needed here...
    // Consider rewrite again sans categorical flair.

    def algebraicFun[T](algebra: Algebra[T]): T => T = x => body match {
      case body: ADT => replaceMe(x, algebra, body)
    }

    def paramorphicFun[T](morphism: (ADT, Functor[T]) => T): T => T =
      x => body match {
        case body: ADT => replaceMe(x, morphism, body)
      }

    lazy val name: String = body match {
      case body: ADT => christianMe(body)
    }

    private
    def replaceMe[T](x: T, algebra: Algebra[T], body: ADT) =
      body.fold[T] {
        // can't believe I resort to string comparison at the end...
        // somehow reference equality doesn't work.
        case y: Bound[_] if y.binder.name eq this.name => x
        case otherwise => algebra(otherwise)
      }

    private
    def replaceMe[T](x: T, morphism: (ADT, Functor[T]) => T, body: ADT) =
      body.para[T] {
        // downgrading to string comparison is ridiculous.
        // maybe we should do this "member case object" thing?
        // but if reference comparison always fails, could
        // inner case object identity possibly succeed?
        case (_, y: Bound[_]) if y.binder.name == this.name => x
        case (z, f) => morphism(z, f)
      }

    private
    def christianMe(body: ADT): String = {
      // - Do you renounce Satan?
      // - I do renounce him.
      val usedNames: Set[String] =
        // - And all his works?
        body.traverse.flatMap({
          // - I do renounce them.
          case ADT(binder: Binder[_]) => Some(binder.name)
          case _ => None
        })(collection.breakOut)
      var myName = defaultName
      var startingIndex = -1
      var i = startingIndex
      // - And all his pomps?
      while (usedNames contains myName) {
        // - I do renounce them.
        i = i + 1
        if (i == startingIndex)
          sys error "oops, I've renounced everything."
        myName = defaultName + i
      }
      // - Will you be baptized?
      // - I will.
      // - In nomine Patri, et Filii, et Spiritus Sancti,
      //   Michael Rizzi, go in peace.
      myName
    }

    // encoding paramorphisms over an unknown functor
    // by... mutation!
    private trait Status
    private case object IDontKnow extends Status
    private case object Looking extends Status

    private var myHashCode: Int = 0
    private var myHashStatus: Status = IDontKnow

    override lazy val hashCode: Int = myHashStatus match {
      case Looking => myHashCode
      case IDontKnow =>
        myHashStatus = Looking
        myHashCode   = MurmurHash3.seqHash(List(
          getClass.hashCode,
          body.hashCode
        ))
        myHashCode
    }

    private var comparingTo: Binder[T] = null
    private var eqStatus: Status = IDontKnow

    override def equals(other: Any): Boolean = other match {
      case other: Binder[T] =>
        eqStatus match {
          case IDontKnow =>
            comparingTo = other
            eqStatus    = Looking
            val result  = equals(other)
            comparingTo = null
            eqStatus    = IDontKnow
            result
          case Looking =>
            comparingTo eq other
        }

      case _ => false
    }
  }

  trait BinderFactory {
    def newBinder(defaultName: String): Binder[ADT]
    def extractBinder[T](e: Functor[T]): Option[(Binder[T], T)]

    def apply(body: Binder[ADT] => ADT): ADT = apply("x")(body)

    def apply(defaultName: String)(body: Binder[ADT] => ADT): ADT = {
      val result = newBinder(defaultName)
      result.body = body(result)
      ADT(result)
    }

    def unapply[T](e: Functor[T]): Option[(String, T)] = {
      val maybe: Option[(Binder[T], T)] = e match {
        case ADT(unroll) => extractBinder[ADT](unroll)
        case _           => extractBinder(e)
      }
      maybe map {
        case (binder, result) => (binder.name, result)
      }
    }
  }
}

trait Syntax extends NameBindingLanguage {
  override
  def fmap[T, R](f: T => R): Functor[T] => Functor[R] = {
    case Con(s)       => Con._Con(s)
    case Var(x)       => Var._Var(x)
    case Abs(x, body) => Abs._Abs(x, f(body))
    case App(fn, arg) => App._App(f(fn), f(arg))
    case otherwise    => super.fmap(f)(otherwise)
  }

  implicit def stringToGlobalConstant(s: String): ADT = Con(s)

  object Con {
    case class _Con[T](x: String) extends Functor[T]
    def apply(x: String): ADT = ADT(_Con(x))
    def unapply[T](e: Functor[T]): Option[String] = e match {
      case ADT(unroll) => unapplyUnrolled(unroll)
      case _           => unapplyUnrolled(e)
    }

    private[this]
    def unapplyUnrolled[T](e: Functor[T]): Option[String] = e match {
      case i: _Con[T] => _Con.unapply(i)
      case _          => None
    }
  }

  object Var {
    case class _Var[T](binder: Binder[ADT]) extends Bound[T]
    def apply(x: Binder[ADT]): ADT = ADT(_Var(x))
    def unapply[T](e: Functor[T]): Option[Binder[ADT]] = e match {
      case ADT(unroll) => unapplyUnrolled(unroll)
      case _           => unapplyUnrolled(e)
    }

    private[this]
    def unapplyUnrolled[T](e: Functor[T]): Option[Binder[ADT]] = e match {
      case i: _Var[T] => _Var.unapply(i)
      case _          => None
    }
  }

  object App {
    case class _App[T](fn: T, arg: T) extends Functor[T]
    def apply(fn: ADT, arg: ADT): ADT = ADT(_App(fn, arg))
    def unapply[T](e: Functor[T]): Option[(T, T)] = e match {
      case ADT(unroll) => unapplyUnrolled(unroll)
      case _           => unapplyUnrolled(e)
    }

    private[this]
    def unapplyUnrolled[T](e: Functor[T]): Option[(T, T)] = e match {
      case i: _App[T] => _App.unapply(i)
      case _          => None
    }
  }

  object Abs extends BinderFactory {
    case class _Abs[T](defaultName: String, var body: T) extends Binder[T]
    def newBinder(defaultName: String): Binder[ADT] =
        _Abs[ADT](defaultName, null)
    def extractBinder[T](e: Functor[T]): Option[(Binder[T], T)] =
      e match {
        case i: _Abs[T] => _Abs.unapply(i) map (x => (i, x._2))
        case _          => None
      }
  }
}

// copied from cata.scala
trait Values {
  trait Val {
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
    def apply(v: Val): Val = f match {
      case Fun(f) => f(this)(v)
      case _ => Placeholder
    }
  }

  // placeholder
  case object Placeholder extends Val {
    def apply(arg: Val): Val = this
  }

  def liftVal2(f: (Int, Int) => Int): Fun = Fun {
    case Num(m) => Fun { case Num(n) => Num(f(m, n)) }
    case _ => Placeholder
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

trait LambdaCalculus extends Syntax with Values {
  def eval(t: ADT): Val = t para morphicEval

  def morphicEval: (ADT, Functor[Val]) => Val = {
    case (ADT(abs: Abs._Abs[_]), _) =>
      Fun(abs paramorphicFun morphicEval)

    case (_, Con(s)) =>
      lookupVal(s)

    case (_, App(f, x)) =>
      f(x)

    case (_, Var(_)) =>
      Placeholder

    case (x, _) =>
      sys error s"No clue how to evaluate $x"
  }

  def pretty(t: ADT): String = t para morphicPretty

  /** extension point: pretty print */
  def morphicPretty: (ADT, Functor[String]) => String = {
    case (Con(s), _)  => s
    case (Var(x), _)  => x.name
    case (Abs(x, body), _) => s"(λ$x. ${body para morphicPretty})"
    case (_, App(fn, arg)) => s"($fn $arg)"
    case x => sys error s"No clue how to pretty-print $x"
  }
}

class Test extends LambdaCalculus {
  val twoPlusTwo: ADT = App(App("+", "2"), "2")

  val id: ADT = Abs { x => Var(x) }

  val const: ADT = Abs { x => Abs { y => Var(x) } }

  val sum: ADT =
     App(
       App("fix", Abs(f => Abs(n =>
         App(App(App("if0", Var(n)),
           Abs(_ => "0")),
           Abs(_ => App(App("+", Var(n)),
                      App(Var(f), App(App("-", Var(n)), "1")))))))),
     "10")

  val fac: ADT =
    App(
      App("fix", Abs(f => Abs(n =>
        App(App(App("if0", Var(n)),
          Abs(_ => "1")),
          Abs(_ => App(App("*", Var(n)),
                     App(Var(f), App(App("-", Var(n)), "1")))))))),
      "5")


  def test(t: => ADT) {
    println(s"${pretty(t)} = ${eval(t)}")
    println()
  }

  test(twoPlusTwo)
  test(id)
  test(const)

  // fix-point operator doesn't work yet.
  println(pretty(sum))
  println(pretty(fac))
}

new Test
