trait WantToWrite {
  trait Term

  // a case class with a name as argument is always bound
  case class Var(name: Name) extends Term

  // a case class with a name and a term as argument is
  // always a binder
  case class Abs(name: Name, body: Term) extends Term

  case class App(operator: Term, operand: Term) extends Term

  case class Con(stant: String) extends Term

  // what we don't want to write, but is necessary to type check
  type Name
}
