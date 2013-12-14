trait LambdaCalculus extends LambdaTerms {
  def pretty(t: Term): String = t para prettyMorphism

  def prettyMorphism(t: => Term, f: => TermFunctor[String]): String =
    f match {
      case ConF(stant)   => stant
      case VarF(x)       => x.binder.name
      case AbsF(x, body) => s"(λ${x.name}. $body)"
      case AppF(fn, arg) => s"($fn $arg)"
    }

  type Reduction = TermAlgebra[Term]

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
            Abs("then") { t => Abs("else") { e => App(t, Con("TT")) } }
          else
            Abs("then") { t => Abs("else") { e => App(e, Con("TT")) } }
      }
    }

  def eval(t: Term): Term = leftMostOuterMost(t).fold(t)(eval)

  def leftMostOuterMost(t: Term): Option[Term] = {
    ((beta orElse mu orElse delta) andThen Some.apply).
      applyOrElse[Term, Option[Term]](
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

  val twoPlusTwo: Term = App(App("+", "2"), "2")

  val id: Term = Abs { x => x }

  val const: Term = Abs("x") { x => Abs("y") { y => x } }

  val auto: Term = Abs { x => App(x, x) }

  val sum: Term =
     App(
       App("fix", Abs("f")(f => Abs("n")(n =>
         App(App(App("if0", n),
           Abs("_")(_ => "0")),
           Abs("_")(_ => App(App("+", n),
                      App(f, App(App("-", n), "1")))))))),
     "10")

  val fac: Term =
    App(
      App("fix", Abs("f")(f => Abs("n")(n =>
        App(App(App("if0", n),
          Abs("_")(_ => "1")),
          Abs("_")(_ => App(App("*", n),
                     App(f, App(App("-", n), "1")))))))),
      "5")

  def test(t: => Term) {
    println(s"${pretty(t)} = ${eval(t)}\n")
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

object TestWhatWeHaveToWrite {
  def main(args: Array[String]){
    val v = new Test with ValueSemantics    { type Domain = Val }
    val r = new Test with ReductionSemantics{ type Domain = ADT }
    v.testAll
    r.testAll
  }
}
