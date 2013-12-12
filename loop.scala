trait Term

case class Abs(var body: Term) extends Term

case class Var(val name: Term) extends Term {
  override def toString: String = "x"

  override def equals(that: Any): Boolean = that match {
    case that: Var => this matches that.name
    case _         => false
  }

  def matches(name: Term): Boolean = name eq this.name
}

def lambda(body: Term => Term): Term = {
  val result = Abs(null)
  result.body = body(result)
  result
}

val id1 = lambda(x => Var(x))
val id2 = lambda(x => Var(x))

id1 == id2 // is false unfortunately
