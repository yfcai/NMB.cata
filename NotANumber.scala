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

  abstract class FreeName(genus: Genus) extends Tag(genus)
  abstract class DeBruijn(genus: Genus) extends Tag(genus)
  abstract class Binder(
    val prison    : DeBruijn,
    myGenus       : Genus,
    bodyGenus     : Genus,
    extraSubgenera: Genus*
  ) extends
      Tag(myGenus, String +: bodyGenus +: extraSubgenera: _*)
  {
    def        bodyOf(t: Tree): Tree   = t.children.tail.head
    def defaultNameOf(t: Tree): String = t.children.head match {
      case §(x) => x
    }

    // name discovery in a namespace
    def nameOf(t: Tree): String = {
      val toAvoid = t.freeNames ++
        crossedNames(bodyOf(t), 0).fold(Set.empty[String])(identity)
      val startingID  = -1
      val defaultName = defaultNameOf(t)
      var i = startingID
      var x = defaultName
      while (toAvoid contains x) {
        i = i + 1
        if (i == startingID) sys error "ran outta names"
        x = defaultName + i
      }
      x
    }

    // names of binders crossing a back-reference path
    // with the same prison
    def crossedNames(t: Tree, i: Int): Option[Set[String]] = t match {
      case ⊹(tag: Binder, children @ _*) =>
        collectOptions(children.map(x => crossedNames(x, i + 1)))(_ ++ _).
          map { x =>
            if (tag.prison == this.prison) // name-spacing
              x + tag.nameOf(t)
            else
              x
          }
      case ⊹(tag, children @ _*) =>
        collectOptions(children map { x => crossedNames(x, i) })(_ ++ _)
      case ∙(tag: DeBruijn, j) if j == i =>
        Some(Set.empty[String])
      case _ =>
        None
    }

    def collectOptions[S](x: Seq[Option[S]])(op: (S, S) => S): Option[S] = {
      val existing = x withFilter (_ != None) map (_.get)
      if (existing.isEmpty)
        None
      else
        Some(existing.tail.fold(existing.head)(op))
    }
  }

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

    // substitution of variable bound here
    // (only works on binders)
    def apply(xdef: Tree): Tree = {
      require(tag.isInstanceOf[Binder])
      tag match { case tag: Binder =>
        tag bodyOf this subst (0, xdef)
      }
    }

    // substitution of bound variable
    def subst(i: Int, xdef: Tree): Tree = this match {
      case ⊹(tag: Binder, children @ _*) =>
        ⊹(tag, children map (_.subst(i + 1, xdef)): _*)
      case ⊹(tag, children @ _*) =>
        ⊹(tag, children map (_.subst(i, xdef)): _*)
      case ∙(tag: DeBruijn, j: Int) if i == j =>
        require(xdef.tag.genus == tag.genus)
        xdef.shift(i, 0)
      case ∙(tag, get) =>
        ∙(tag, get)
    }

    // put a free variable in prison, give it numbers
    def imprison(prison: DeBruijn, x: String, i: Int): Tree =
      this match {
        case ⊹(tag: Binder, children @ _*) =>
          ⊹(tag, children map (_.imprison(prison, x, i + 1)): _*)
        case ⊹(tag, children @ _*) =>
          ⊹(tag, children map (_.imprison(prison, x, i)): _*)
        case ∙(tag: FreeName, get) if get == x =>
          require(tag.genus == prison.genus) // shan't bind typevar by λ
          ∙(prison, i)
        case ∙(tag, get) =>
          ∙(tag, get)
      }

    // d-place shift of t above cutoff c
    def shift(d: Int, c: Int): Tree = this match {
      case ⊹(tag: Binder, children @ _*) =>
        ⊹(tag, children map (_.shift(d, c + 1)): _*)
      case ⊹(tag, children @ _*) =>
        ⊹(tag, children map (_.shift( d, c)): _*)
      case ∙(tag: DeBruijn, j: Int) if j >= c =>
        ∙(tag, j + d)
      case ∙(tag, get) =>
        ∙(tag, get)
    }

    def print: String = print(0, 2)

    def print(indent: Int, increment: Int): String =
      lines(indent, increment, Nil) mkString "\n"

    // primitive tree-like printing
    def lines(indent: Int, increment: Int, env: Seq[String]):
        Seq[String] = {
      def put(x: Any): String = s"${Array.fill(indent)(' ').mkString}$x"
      this match {
        case ⊹(tag: Binder, children @ _*) =>
          val name = tag nameOf this
          s"${put(tag)}, binder of $name" +: (children flatMap {
            _.lines(indent + increment, increment, name +: env)
          })

        case ⊹(tag, children @ _*) =>
          put(tag) +: (children flatMap {
            _.lines(indent + increment, increment, env)
          })

        case ∙(tag: DeBruijn, j: Int) =>
          Seq(s"${put(tag)}, bound of ${env(j)}")

        case _ =>
          Seq(put(this))
      }
    }

    // collect free names with tag equal to mine
    def freeNames: Set[String] = fold[Set[String]] {
      case ∙:(tag: FreeName, get: String) if tag.genus == this.tag.genus =>
        Set(get)
      case ∙:(tag, get) =>
        Set.empty
      case otherwise =>
        allFreeNamesAlgebra(otherwise)
    }

    // collect all free names
    def allFreeNames: Set[String] = fold(allFreeNamesAlgebra)

    def allFreeNamesAlgebra: TreeF[Set[String]] => Set[String] = {
      case ⊹:(tag, children @ _*) =>
        children.fold(Set.empty[String])(_ ++ _)
      case ∙:(tag: FreeName, get: String) =>
        Set(get)
      case _ =>
        Set.empty
    }
  }

  // branches and leafs, worthy of boilerplates
  class ∙[S](tag: Tag, get: S)
      extends ∙:[Tree, S](tag, get) with Tree {
    override def toString = s"∙($tag, $get)"
  }
  class ⊹(tag: Tag, children: Tree*)
      extends ⊹:[Tree](tag, children: _*) with Tree {
    override def toString =
      s"⊹($tag, ${children.map(_.toString).mkString(", ")})"
  }

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
  object § {
    def apply(s: String): ∙[String] = ∙(StringTag, s)
    def unapply(s: ∙[_]): Option[String] = s match {
      case ∙(StringTag, s: String) => Some(s)
      case _ => None
    }
  }

  // terms, no boilerplate
  case object Term extends Genus
  case object FreeVar extends FreeName(Term)
  case object Var extends DeBruijn(Term)
  case object Abs extends Binder(Var, Term, Term)
  case object App extends Tag(Term, Term, Term)

  object λ {
    def apply(x: String)(body: Tree): Tree =
      ⊹(Abs, §(x), body.imprison(Var, x, 0))
  }

  object χ {
    def apply(x: String): Tree =
      ∙(FreeVar, x)
  }
}

object TestNotANumber extends NotANumber {
  val id = λ("x")(χ("x"))
  val const = λ("x")(λ("y")(χ("x")))

  def main(args: Array[String]) {
    println(id.print)
    println(const.print)
    println(const(id).print)
  }
}
