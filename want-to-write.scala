trait WantToWrite {
  trait Term

  // a case class with a binder as argument is always bound
  case class Var(binder: Binder) extends Term

  // a case class with a binder and a term as argument is
  // always a binder
  case class Abs(binder: Binder, body: Term) extends Term

  case class App(operator: Term, operand: Term) extends Term

  case class Con(stant: String) extends Term

  // what we don't want to write, but is necessary to type check
  type Binder
}
