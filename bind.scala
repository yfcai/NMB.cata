import scala.language.implicitConversions

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

  case class ParaADT(functor: Functor[(ADT, ParaADT)]) {
    def fold[T](f: (=> ADT, => Functor[T]) => T): T =
      f(functor.map(_._1).toADT, functor map { _._2 fold f})
  }

  // We cheat out of the boilerplates of yet another functor
  // by mutation.
  object ParaADT {
    def apply(adt: ADT): ParaADT = {
      var traversed = adt.traverse
      adt.fold[(ADT, ParaADT)]({
        case functor =>
          val result = (traversed.head, ParaADT(functor))
          traversed = traversed.tail
          result
      })._2
    }
  }

  object ADT {
    // anamorphism
    def ana[T](psi: Coalgebra[T])(x: T): ADT = (psi(x) map (ana(psi))).toADT
  }

  trait ADT extends Functor[ADT] {
    // catamorphism
    def fold[T](f: Algebra[T]): T = f(this map (_ fold f))

    // paramorphism.
    // if a normal function (not a case function) is given as argument,
    // then para does not recurse unless necessary.
    // this is important if the ADT has a cycle.
    def para[T](f: (=> ADT, => Functor[T]) => T): T = ParaADT(this) fold f

    def subst(from: Binder, to: ADT): ADT = subst(Map(from -> to))

    def subst(env: Map[Binder, ADT]): ADT = para[ADT] { (before, after) =>
      before match {
        case binder: Binder if env isDefinedAt binder =>
          binder subst (env - binder)
        case _ => after match {
          case y: Bound[_] if env.isDefinedAt(y.binder) => env(y.binder)
          case otherwise => otherwise.toADT
        }
      }
    }

    def pretty: String = para(prettyMorphism)

    /** gives a list of ADTs in traversal order */
    def traverse: List[ADT] = {
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
    def bound(binder: Binder): ADT with Bound[ADT]

    def apply(body: ADT => ADT): T = {
      val binder = newBinder
      binder.body = body(bound(binder))
      binder
    }

    def apply(defaultName: String)(body: ADT => ADT): T = {
      val binder = newBinder
      binder.defaultName = defaultName
      binder.body = body(bound(binder))
      binder
    }

    def unapply(b: T): Option[(Binder, ADT)] = Some((b.binder, b.body))

    def replaceBody(binder: Binder, body: ADT): Binder =
      apply(binder.defaultName) { x => body.subst(binder, x) }
  }

  trait Binder extends ADT {
    // inherited from case class
    var binder: Binder
    var body: ADT

    // cleverly loop to self
    binder = this

    lazy val name: String = christianMe(body)

    def apply(arg: ADT): ADT = (toFun[ADT] { case x => x.toADT })(arg)

    def toFun[T](algebra: Algebra[T]): T => T = x => body.fold[T] {
      case y: Bound[_] if y.binder == this => x
      case otherwise => algebra(otherwise)
    }

    private[NameBindingLanguage]
    var defaultName: String = "x"

    private def christianMe(body: ADT): String = {
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
    private[NameBindingLanguage]
    var thisHashCode: Int = -1

    def nextHashCode(): Int = {
      thisHashCode += 1
      thisHashCode
    }
  }

  def prettyMorphism(t: => ADT, s: => Functor[String]): String = t.toString
}

trait Syntax extends NameBindingLanguage {
  override
  def fmap[T, R](f: T => R): Functor[T] => Functor[R] = {
    case ConF(stant)   => ConF(stant)
    case AppF(fn, arg) => AppF(f(fn), f(arg))
    case VarF(binder)  => VarF(binder)
    case AbsF(x, body) => AbsF(x, f(body))
    case otherwise    => super.fmap(f)(otherwise)
  }

  case class AbsF[T](var binder: Binder, var body: T) extends Functor[T] {
    def toADT: ADT = body match {
      case body: ADT => Abs.replaceBody(binder, body)
    }
  }
  class Abs(body: ADT) extends AbsF[ADT](null, body) with Binder {
    override def toADT = this
  }
  object Abs extends BinderFactory[Abs] {
    def newBinder(): Abs = new Abs(null)
    def bound(binder: Binder): Var = Var(binder)
  }

  case class VarF[T](binder: Binder) extends Bound[T]
  { def toADT: ADT = Var(binder) }
  class Var(binder: Binder) extends VarF[ADT](binder) with ADT {
    override def toADT = this
  }
  object Var {
    def apply(binder: Binder): Var = new Var(binder)
    def unapply(v: Var): Option[Binder] = Some(v.binder)
  }

  case class AppF[T](fun: T, arg: T) extends Functor[T] {
    def toADT: ADT = (fun, arg) match {
      case (fun: ADT, arg: ADT) => App(fun, arg)
    }
  }
  class App(fun: ADT, arg: ADT) extends AppF[ADT](fun, arg) with ADT {
    override def toString: String =
      s"${getClass.getSimpleName}($fun, $arg)"
  }
  object App {
    def apply(fun: ADT, arg: ADT): App = new App(fun, arg)
    def unapply(a: App): Option[(ADT, ADT)] = Some((a.fun, a.arg))
  }

  case class ConF[T](stant: String) extends Functor[T]
  { def toADT: ADT = Con(stant) }
  class Con(stant: String) extends ConF[ADT](stant) with ADT {
    override def toString: String =
      s"${getClass.getSimpleName}($stant)"
  }
  object Con {
    def apply(stant: String): Con = new Con(stant)
    def unapply(c: Con): Option[String] = Some(c.stant)
  }

  override def prettyMorphism(t: => ADT, f: => Functor[String]): String =
    f match {
      case ConF(stant)   => stant
      case VarF(x)       => x.binder.name
      case AbsF(x, body) => s"(λ${x.name}. $body)"
      case AppF(fn, arg) => s"($fn $arg)"
      case _             => super.prettyMorphism(t, f)
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

trait ValueSemantics extends Syntax with Values {
  def eval(t: ADT): Val = {
    def withEnv(t: ADT) = t fold evalAlgebra
    withEnv(t)(Map.empty[Binder, Val])
  }

  /** extension point: evaluation operation */
  def evalAlgebra: Algebra[Env[Val] => Val] = {
    case ConF(s)       => _ => lookupVal(s)
    case VarF(x)       => _(x)
    case AppF(fn, arg) => env => fn(env)(arg(env))
    case AbsF(x, body) => env => Fun {
      v => body(({ case y if x == y => v }: Env[Val]) orElse env)
    }
  }
}

trait ReductionSemantics extends Syntax {
  type Reduction = Algebra[ADT]

  override def fmap[T, R](f: T => R): Functor[T] => Functor[R] = {
    case TT() => TT()
    case otherwise => super.fmap(f)(otherwise)
  }
  case class TT[T]() extends Functor[T] { def toADT = TT }
  object TT extends TT[ADT]() with ADT

  val beta: Reduction = {
    case AppF(f: Abs, arg) => f(arg)
  }

  val mu: Reduction = {
    case AppF(Con("fix"), f) => App(f, App(Con("fix"), f))
  }

  val delta: Reduction =
    liftOp2("+", _+_) orElse liftOp2("-", _-_) orElse
    liftOp2("*", _*_) orElse liftOp2("/", _/_) orElse {
      case AppF(Con("if0"), n) => eval(n) match {
        case Con(n) =>
          if (n.toInt == 0)
            Abs("then") { t => Abs("else") { e => App(t, TT) } }
          else
            Abs("then") { t => Abs("else") { e => App(e, TT) } }
      }
    }

  def eval(t: ADT): ADT = leftMostOuterMost(t).fold(t)(eval)

  def leftMostOuterMost(t: ADT): Option[ADT] = {
    ((beta orElse mu orElse delta) andThen Some.apply).
      applyOrElse[ADT, Option[ADT]](
        t, {
          case App(fun, arg) =>
            leftMostOuterMost(fun) map { f => App(f, arg) }
          case _ =>
            None
        })
  }

  def liftOp2(symbol: String, op: (Int, Int) => Int): Reduction = {
    case AppF(App(Con(opName), lhs), rhs)
        if opName == symbol =>
      (eval(lhs), eval(rhs)) match {
        case (Con(lhs), Con(rhs)) =>
          Con((op(lhs.toInt, rhs.toInt)).toString)
      }
  }
}

trait TestSubjects extends Syntax {
  val twoPlusTwo: ADT = App(App("+", "2"), "2")

  val id: ADT = Abs { x => x }

  val const: ADT = Abs("x") { x => Abs("y") { y => x } }

  val auto: ADT = Abs { x => App(x, x) }

  val sum: ADT =
     App(
       App("fix", Abs("f")(f => Abs("n")(n =>
         App(App(App("if0", n),
           Abs("_")(_ => "0")),
           Abs("_")(_ => App(App("+", n),
                      App(f, App(App("-", n), "1")))))))),
     "10")

  val fac: ADT =
    App(
      App("fix", Abs("f")(f => Abs("n")(n =>
        App(App(App("if0", n),
          Abs("_")(_ => "1")),
          Abs("_")(_ => App(App("*", n),
                     App(f, App(App("-", n), "1")))))))),
      "5")
}

trait Test extends TestSubjects {
  type Domain

  def eval(t: ADT): Domain

  def test(t: => ADT) {
    println(s"${t.pretty} = ${eval(t)}\n")
  }

  def testAcyclic() {
    test(twoPlusTwo)
    test(const)
    test(App(id, Con("19")))
    test(App(const, Con("97")))
    test(App(App(const, id), Con("71")))
    test(App(id, id))
  }

  def testRecurse() {
    test(App(Con("fix"), Abs("f") { f => Con("1997") }))
    test(App(Con("fix"), Abs("f") { f => Abs { x => x } }))
    test(sum)
    test(fac)
  }

  def testSelfApp() {
    test(auto)
    test(App(auto, id))
    test(App(App(App(auto, App(auto, id)), id), Con("42")))
  }

  def testAll() {
    testAcyclic()
    testRecurse()
    testSelfApp()
  }
}

object TestSemantics {
  def main(args: Array[String]){
    val v = new Test with ValueSemantics    { type Domain = Val }
    val r = new Test with ReductionSemantics{ type Domain = ADT }
    v.testAcyclic
    v.testRecurse
    v.testSelfApp

    r.testAcyclic
    r.testRecurse
    r.testSelfApp
  }
}
