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

    def toADT: ADT
  }

  object ADT {
    // anamorphism
    def ana[T](psi: Coalgebra[T])(x: T): ADT = (psi(x) map (ana(psi))).toADT
  }

  trait ADT extends Functor[ADT] {
    // catamorphism
    def fold[T](f: Algebra[T]): T = f(this map (_ fold f))

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

    def subst(from: Binder, to: ADT): ADT = fold[ADT] {
      case y: Bound[_] if y.binder == from => to
      case otherwise => otherwise.toADT
    }

    //def subst(env: Env[ADT]): ADT =

    /** gives a list of ADTs in traversal order */
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
          val visiting = s.toADT
          traversed = visiting :: traversed
          visiting
      }
      traversed.reverse
    }
  }

  // What... a name-binding language?!

  type Env[T] = PartialFunction[Binder, T]

  // Note the lack of type recursion here
  trait Bound[T] extends Functor[T] {
    def binder: Binder
    override def toString: String = binder.name
  }

  trait BinderFactory[T <: Binder] {
    def newBinder(): T

    def apply(body: Binder => ADT): T = {
      val binder = newBinder
      binder.body = body(binder)
      binder
    }

    def apply(defaultName: String)(body: Binder => ADT): T = {
      val binder = newBinder
      binder.defaultName = defaultName
      binder.body = body(binder)
      binder
    }

    def unapply(b: T): Option[(Binder, ADT)] = Some((b.binder, b.body))
  } 

  trait Binder extends ADT {
    // inherited from case class
    var binder: Binder
    var body: ADT

    // cleverly loop to self
    binder = this

    lazy val name: String = "???"

    def toHoas: ADT => ADT = toFun[ADT] { case x => x.toADT }

    def toFun[T](algebra: Algebra[T]): T => T = x => body.fold[T] {
      case y: Bound[_] if y.binder eq this => x
      case otherwise => algebra(otherwise)
    }

    private[NameBindingLanguage]
    var defaultName: String = "x"

    private def christianMe(body: ADT): String = {
      // - Do you renounce Satan?
      val usedNames: Set[String] =
        // - I do renounce him.
        body.traverse.flatMap({
          // - And all his works?
          case binder: Binder => Some(binder.name)
          case _ => None
        })(collection.breakOut)
      // - I do renounce them.
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

    private var comparingTo: Binder = null
    private var eqStatus: Status = IDontKnow

    override def equals(other: Any): Boolean = other match {
      case other: Binder => other eq this
        eqStatus match {
          case Looking =>
            comparingTo eq other
          case IDontKnow =>
            comparingTo = other
            eqStatus    = Looking
            val result  = body equals other.body
            comparingTo = null
            eqStatus    = IDontKnow
            result
        }

      case _ => false
    }
  }
}

trait Syntax extends NameBindingLanguage {
  override
  def fmap[T, R](f: T => R): Functor[T] => Functor[R] = {
    case ConF(stant)   => ConF(stant)
    case AppF(fn, arg) => AppF(f(fn), f(arg))
    case VarF(binder)  => VarF(binder)
    //case Abs(x, body) => Abs._Abs(x, f(body))
    case otherwise    => super.fmap(f)(otherwise)
  }

  case class AbsF[T](var binder: Binder, var body: T) extends Functor[T]
  { def toADT: ADT = binder }
  class Abs(body: ADT) extends AbsF[ADT](null, body) with Binder
  object Abs extends BinderFactory[Abs]
  { def newBinder(): Abs = new Abs(null) }

  case class VarF[T](binder: Binder) extends Bound[T]
  { def toADT: ADT = Var(binder) }
  class Var(binder: Binder) extends VarF[ADT](binder) with ADT
  object Var {
    def apply(binder: Binder): Var = new Var(binder)
    def unapply(v: Var): Option[Binder] = Some(v.binder)
  }

  case class AppF[T](fun: T, arg: T) extends Functor[T] {
    def toADT: ADT = (fun, arg) match {
      case (fun: ADT, arg: ADT) => App(fun, arg)
    }
  }
  class App(fun: ADT, arg: ADT) extends AppF[ADT](fun, arg) with ADT
  object App {
    def apply(fun: ADT, arg: ADT): App = new App(fun, arg)
    def unapply(a: App): Option[(ADT, ADT)] = Some(a.fun, a.arg)
  }

  case class ConF[T](stant: String) extends Functor[T]
  { def toADT: ADT = Con(stant) }
  class Con(stant: String) extends ConF[ADT](stant) with ADT
  object Con {
    def apply(stant: String): Con = new Con(stant)
    def unapply(c: Con): Option[String] = Some(c.stant)
  }

  implicit def stringToGlobalConstant(s: String): ADT = Con(s)
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

/*
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
*/
