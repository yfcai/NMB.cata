/** Conor McBride and James McKinna:
  * I am not a number---I am a free variable
  */

trait NotANumber {
  trait Genus // type, terms, etc

  abstract class Tag(val genus: Genus, val subgenera: Genus*)

  trait TreeF[T] {
    def tag: Tag
    def children: Seq[T]

    def map[S](f: T => S): TreeF[S] = this match {
      case ∙:(tag, get) => ∙:(tag, get)
      case ⊹:(tag, children @ _*) => ⊹:(tag, children map f: _*)
    }
  }
  case class ∙:[T, S](tag: Tag, get: S)
      extends TreeF[T] { def children = Nil }
  case class ⊹:[T](tag: Tag, children: T*) extends TreeF[T]

  type FreeName = ∙[String]
  abstract class NameTag(genus: Genus) extends Tag(genus, String)
  abstract class DeBruijnIndex(genus: Genus) extends Tag(genus, Int)

  object Tree extends (TreeF[Tree] => Tree) {
    def apply(x: TreeF[Tree]): Tree = x match {
      case ∙:(tag, get) => ∙(tag, get)
      case ⊹:(tag, children @ _*) => ⊹(tag, children: _*)
    }
  }

  trait Tree extends TreeF[Tree] {
    // dynamic type safety, may disable for performance
    require(children.map(_.tag.genus) == tag.subgenera)

    def fold[S](f: TreeF[S] => S): S = f(this map (_ fold f))

    // substitution of free names
    def toHOAS(x: FreeName): Tree => Tree = toFun(x, Tree)

    def toFun[S](x: FreeName, f: TreeF[S] => S): S => S =
      y => fold[S] {
        case ∙:(tag: NameTag, get) if tag == x.tag && get == x.get => y
        case otherwise => f(otherwise)
      }
  }

  // branches and leafs, worthy of boilerplates
  class ∙[S](tag: Tag, get: S)
      extends ∙:[Tree, S](tag, get) with Tree
  class ⊹(tag: Tag, children: Tree*)
      extends ⊹:[Tree](tag, children: _*) with Tree

  object ∙ {
    def apply[S](tag: Tag, get: S): ∙[S] = new ∙(tag, get)
    def unapply[S](x: ∙[S]): Option[(Tag, S)] = Some((x.tag, x.get))
  }
  object ⊹ {
    def apply(tag: Tag, children: Tree*): ⊹ = new ⊹(tag, children: _*)
    def unapplySeq(y: ⊹): Option[(Tag, Seq[Tree])] =
      Some((y.tag, y.children))
  }

  // string literals
  case object String extends Genus
  case object StringTag extends Tag(String)
  class §(get: String) extends ∙(StringTag, get) {
    override def toString = s"§($get)"
  }
  object § {
    def apply(s: String): § = new §(s)
    def unapply(s: §): Option[String] = Some(s.get)
  }

  // int literals, hopefully the last boilerplate
  case object Int extends Genus
  case object IntTag extends Tag(Int)
  class ӥ(get: Int) extends ∙(IntTag, get) {
    override def toString = get.toString
  }
  object ӥ {
    def apply(i: Int): ӥ = new ӥ(i)
    def unapply(i: ӥ): Option[Int] = Some(i.get)
  }

  // terms, no boilerplate
  case object Term extends Genus
  case object FreeVar extends NameTag(Term)
  case object Var extends DeBruijnIndex(Term)
  case object Abs extends Tag(Term, String, Term)
  case object App extends Tag(Term, Term, Term)

  object λ {
    def apply(defaultName: String)(body: Tree => Tree): Tree = {
      ???
    }
  }
}
